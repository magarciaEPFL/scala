/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{ProdConsAnalyzer, UnBoxAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/*
 *  Utilities shared across intra-method and inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptCommon extends BCodeTypes {

  import global._

  trait BCodeCleanserIface {
    def intraMethodFixpoints(full: Boolean)
  }

  trait QuickCleanserIface {
    def basicIntraMethodOpt(mnode: asm.tree.MethodNode)
  }

  /*
   *  Single-access point for requests to parse bytecode for inlining purposes.
   *  Given the BType of a class with internal name,
   *  `codeRepo` allows obtaining its bytecode-level representation (ClassNode).
   *  It's possible to find out whether a ClassNode was compiled in this run, or parsed from an external library.
   */
  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = { (classes.containsKey(bt) || parsed.containsKey(bt)) }

    /*
     *  must-single-thread
     */
    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    /*
     *  must-single-thread
     */
    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /*
     *  @return None if not found, the MethodNode's access field otherwise.
     *
     *  must-single-thread
     *
     */
    def getMethodAccess(bt: BType, name: String, desc: String): Option[Int] = {
      val cn = getClassNode(bt) // must-single-thread
      if(cn == null) { return None }
      val iter = cn.methods.iterator()
      while(iter.hasNext) {
        val mn = iter.next()
        if(mn.name == name && mn.desc == desc) {
          return Some(mn.access)
        }
      }
      for(ifaceIName <- JListWrapper(cn.interfaces)) {
        val outcome = getMethodAccess(lookupRefBType(ifaceIName), name, desc)
        if(outcome.nonEmpty) { return outcome }
      }
      if(cn.superName != null) {
        val outcome = getMethodAccess(lookupRefBType(cn.superName), name, desc)
        if(outcome.nonEmpty) { return outcome }
      }
      None
    }

    /*
     * Looks up (parsing from bytecode if needed) the field declared in `bt`
     * given by the combination of field-name and field-descriptor.
     *
     * must-single-thread
     */
    def getField(bt: BType, name: String, desc: String): FieldNode = {
      val cn = getClassNode(bt)
      val iter = cn.fields.iterator()
      while(iter.hasNext) {
        val fn = iter.next()
        if(fn.name == name && fn.desc == desc) {
          return fn
        }
      }

      MissingRequirementError.notFound(s"Could not find FieldNode: ${bt.getInternalName}.$name: ${desc}")
    }

    /*
     * Looks up (parsing from bytecode if needed) the method declared in `bt`
     * given by the combination of method-name and method-descriptor.
     * Keeps looking up over the superclass hierarchy, until reaching j.l.Object
     *
     * @return if found, the MethodNode and the ClassNode declaring it. Otherwise MissingRequirementError is thrown.
     *
     * must-single-thread
     */
    def getMethod(bt: BType, name: String, desc: String): MethodNodeAndOwner = {

      var current = bt

      while(current != null) {
        val cn = getClassNode(current)
        val iter = cn.methods.iterator()
        while(iter.hasNext) {
          val mn = iter.next()
          if(mn.name == name && mn.desc == desc) {
            return MethodNodeAndOwner(mn, cn)
          }
        }
        current = if(cn.superName == null) null else lookupRefBType(cn.superName)
      }

      MissingRequirementError.notFound(s"Could not find MethodNode: ${bt.getInternalName}.${name}${desc}")
    }

    /* must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = { getClassNode(brefType(owner)) }

    /*
     *  Returns the ASM ClassNode for a class that's being compiled or that's going to be parsed from external bytecode.
     *
     *  After this method has run, the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.containsKey(bt)`
     *
     *  must-single-thread
     */
    def getClassNode(bt: BType): asm.tree.ClassNode = {
      var res = classes.get(bt)
      if(res == null) {
        res = parsed.get(bt)
        if(res == null) {
          res = parseClassAndEnterExemplar(bt)
        }
      }
      assert(exemplars.containsKey(bt))
      res
    }

    /*  can-multi-thread*/
    def getClassNodeOrNull(bt: BType): asm.tree.ClassNode = {
      try {
        var res = classes.get(bt)
        if(res == null) {
          res = parsed.get(bt)
          // we can't call parseClassAndEnterExemplar(bt) because in the time window from the checks above and
          // the time parseClassAndEnterExemplar() runs, Worker1 may have added to codeRepo.classes the class we didn't find.
        }
        res
      }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /*
     *  Some analyses (e.g., Type-Flow Analysis) and some backend utilities (e,g, `refreshInnerClasses()`)
     *  require `exemplars` to contain entries for all classes the analysis encounters.
     *  A class that is being compiled is already associated to a Tracked instance (GenBCode took care of that).
     *  For a class `bt` mentioned in external bytecode, `parseClassAndEnterExemplar()` adds an entry to `exemplars`.
     *
     *  After this method has run the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.parsed.containsKey(bt)`
     *
     *  @param bt a "normal" class (see `BType.isNonSpecial`) for which an entry in `exemplars` should be added if not yet there.
     *
     *  @return   the ASM ClassNode after parsing the argument from external bytecode.
     *
     *  must-single-thread
     */
    def parseClassAndEnterExemplar(bt: BType): ClassNode = {
      assert(bt.isNonSpecial,  s"The `exemplars` map is supposed to hold ''normal'' classes only, not ${bt.getInternalName}")
      assert(!containsKey(bt), s"codeRepo already contains ${bt.getInternalName}")

          /* must-single-thread */
          def parseClass(): asm.tree.ClassNode = {
            assert(!containsKey(bt))
            val iname   = bt.getInternalName
            val dotName = iname.replace('/', '.')
            classPath.findSourceFile(dotName) match {
              case Some(classFile) =>
                val cn = new asm.tree.ClassNode()
                val cr = new asm.ClassReader(classFile.toByteArray)
                cr.accept(cn, asm.ClassReader.SKIP_FRAMES)
                parsed.put(bt, cn)
                cn
              case _ => MissingRequirementError.notFound(s"Could not find bytecode for $dotName")
            }
          }

      val cn = parseClass()

      if(exemplars.containsKey(bt)) {
        return cn // TODO check if superName, interfaces, etc agree btw cn and exemplar(bt)
      }

          def enterIfUnseen(iname: String): Tracked = {
            val bt = brefType(iname)
            var exempl = exemplars.get(bt)
            if(exempl == null) {
              parseClassAndEnterExemplar(bt) // recursive call
              exempl = exemplars.get(bt)
            }
            exempl
          }

          def enterIfUnseens(inames: java.util.List[String]): Array[Tracked] = {
            var ifaces: List[Tracked] = Nil
            val iter = inames.iterator()
            while(iter.hasNext) {
              ifaces ::= enterIfUnseen(iter.next())
            }
            if(ifaces.isEmpty) { EMPTY_TRACKED_ARRAY }
            else {
              val arr = new Array[Tracked](ifaces.size)
              ifaces.copyToArray(arr)
              arr
            }
          }

      val tsc       = enterIfUnseen(cn.superName)
      val ifacesArr = enterIfUnseens(cn.interfaces)

      // ClassNode.innerClasses isn't indexed by InnerClassNode.name, this map accomplishes that feat.
      val innerClassNode: Map[String, InnerClassNode] = {
        JListWrapper(cn.innerClasses) map (icn => (icn.name -> icn)) toMap
      }

      val isInnerClass = innerClassNode.contains(cn.name)
      val innersChain: Array[InnerClassEntry] =
        if(!isInnerClass) null
        else {

              def toInnerClassEntry(icn: InnerClassNode): InnerClassEntry = {
                InnerClassEntry(icn.name, icn.outerName, icn.innerName, icn.access)
              }

          var chain: List[InnerClassEntry] = toInnerClassEntry(innerClassNode(cn.name)) :: Nil
          var keepGoing = true
          do {
            // is the enclosing class of the current class itself an inner class?
            val currentOuter = chain.head.outerName
            keepGoing = innerClassNode.contains(currentOuter)
            if(keepGoing) {
              chain ::= toInnerClassEntry(innerClassNode(currentOuter))
            }
          } while(keepGoing)

          chain.toArray
        }

      val tr = Tracked(bt, cn.access, tsc, ifacesArr, innersChain)
      exemplars.put(tr.c, tr) // no counterpart in symExemplars, that's life.

      cn
    }

    /*
     *  This method goes over its argument looking for not-yet-seen TypeNames,
     *  fabricating a Tracked instance for them (if needed by parsing bytecode,
     *  thus the location of this method as utility in codeRepo).
     *
     *  An invariant we want to maintain:
     *    "each internal name mentioned in an instruction that's part of this program
     *     should be associated to a Tracked instance (which implies, associated to a BType instance)"
     *  That invariant guarantees a Type-Flow Analysis can be run anytime,
     *  additionally `refreshInnerClasses()` also relies on `exemplars`.
     *
     *  Without a TypeName for an internal name or method descriptor, the following conversions can't be performed:
     *    from type-descriptor to BType, via `BCodeTypes.descrToBType()`
     *    from internal-name   to BType, via `BCodeTypes.lookupRefBType()`
     *  In turn, BTypes are indispensable as keys to the `exemplars` map.
     *
     *  must-single-thread
     */
    def registerUnseenTypeNames(insns: InsnList) {

        def enterInternalName(iname: String) {
          var bt = brefType(iname)
          if(bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.isNonSpecial && !exemplars.containsKey(bt)) {
            // exemplars can be added *via parsing bytecode* only after all classes being compiled have landed in codeRepo.classes
            codeRepo.parseClassAndEnterExemplar(bt)
          }
        }

        def enterDescr(desc: String) {
          val c: Char = desc(0)
          c match {
            case 'V' | 'Z' | 'C' | 'B' | 'S' | 'I' | 'F' | 'J' | 'D' => ()
            case 'L' =>
              val iname = desc.substring(1, desc.length() - 1)
              enterInternalName(iname)
            case '(' =>
              val mt = BType.getMethodType(desc)
              enterDescr(mt.getReturnType.getDescriptor)
              for(argt <- mt.getArgumentTypes) {
                enterDescr(argt.getDescriptor)
              }
            case '[' =>
              val arrt = BType.getType(desc)
              enterDescr(arrt.getComponentType.getDescriptor)
          }
        }

      val iter = insns.iterator()
      while(iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => enterInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => enterInternalName(fi.owner); enterDescr(fi.desc)
          case mi: MethodInsnNode => enterInternalName(mi.owner); enterDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => enterDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => enterDescr(ma.desc)
          case _ => ()
        }
      }

    } // end of method enterExemplarsForUnseenTypeNames()

    def clear() {
      parsed.clear()
      classes.clear()
    }

  } // end of object codeRepo

  /*
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

  //--------------------------------------------------------
  // helpers to produce logging messages
  //--------------------------------------------------------

  final def methodSignature(ownerIName: String, methodName: String, methodDescriptor: String): String = {
    ownerIName + "::" + methodName + methodDescriptor
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodDescriptor: String): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodDescriptor)
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodType: BType): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodType.getDescriptor)
  }

  final def methodSignature(ownerIName: String, mnode: MethodNode): String = {
    methodSignature(ownerIName, mnode.name, mnode.desc)
  }

  final def methodSignature(ownerBT: BType, mnode: MethodNode): String = {
    methodSignature(ownerBT, mnode.name, mnode.desc)
  }

  final def methodSignature(cnode: ClassNode, mnode: MethodNode): String = {
    methodSignature(lookupRefBType(cnode.name), mnode.name, mnode.desc)
  }

  final def insnPos(insn: AbstractInsnNode, mnode: MethodNode): String = {
   s"${Util.textify(insn)} at index ${mnode.instructions.indexOf(insn)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, cnode: ClassNode): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(cnode, mnode)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, ownerIName: String): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(ownerIName, mnode)}"
  }

} // end of class BCodeOptCommon