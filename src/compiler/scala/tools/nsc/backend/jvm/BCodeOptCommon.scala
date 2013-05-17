/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.optimiz.Util
import asm.tree._

import scala.collection.{ mutable, immutable }

/*
 *  Utilities shared across intra-method and inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptCommon extends BCodeHelpers {

  trait BCodeCleanserIface {
    def intraMethodFixpoints(full: Boolean)
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
