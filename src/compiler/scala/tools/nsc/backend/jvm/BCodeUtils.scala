/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.jvm

import java.nio.ByteBuffer
import scala.collection.{ mutable, immutable }
import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }
import scala.tools.nsc.symtab._
import scala.tools.nsc.io.AbstractFile

import scala.tools.asm
import asm.Label

/**
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *
 */
abstract class BCodeUtils extends SubComponent {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  var pickledBytes = 0 // statistics

  /*
   * Custom attribute (JVMS 4.7.1) "ScalaSig" used as marker only
   * i.e., the pickle is contained in a custom annotation, see:
   *   (1) `addAnnotations()`,
   *   (2) SID # 10 (draft) - Storage of pickled Scala signatures in class files, http://www.scala-lang.org/sid/10
   *   (3) SID # 5 - Internals of Scala Annotations, http://www.scala-lang.org/sid/5
   * That annotation in turn is not related to the "java-generic-signature" (JVMS 4.7.9)
   * other than both ending up encoded as attributes (JVMS 4.7)
   * (with the caveat that the "ScalaSig" attribute is associated to some classes,
   * while the "Signature" attribute can be associated to classes, methods, and fields.)
   *
   **/
  trait BCPickles {

    import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }

    val versionPickle = {
      val vp = new PickleBuffer(new Array[Byte](16), -1, 0)
      assert(vp.writeIndex == 0, vp)
      vp writeNat PickleFormat.MajorVersion
      vp writeNat PickleFormat.MinorVersion
      vp writeNat 0
      vp
    }

    def createJAttribute(name: String, b: Array[Byte], offset: Int, len: Int): asm.Attribute = {
      val dest = new Array[Byte](len);
      System.arraycopy(b, offset, dest, 0, len);
      new asm.CustomAttr(name, dest)
    }

    def pickleMarkerLocal = {
      createJAttribute(tpnme.ScalaSignatureATTR.toString, versionPickle.bytes, 0, versionPickle.writeIndex)
    }

    def pickleMarkerForeign = {
      createJAttribute(tpnme.ScalaATTR.toString, new Array[Byte](0), 0, 0)
    }

    /** Returns a ScalaSignature annotation if it must be added to this class, none otherwise.
     *  This annotation must be added to the class' annotations list when generating them.
     *
     *  Depending on whether the returned option is defined, it adds to `jclass` one of:
     *    (a) the ScalaSig marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is present in this class); or
     *    (b) the Scala marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is to be found in another file).
     *
     *
     *  @param jclassName The class file that is being readied.
     *  @param sym    The symbol for which the signature has been entered in the symData map.
     *                This is different than the symbol
     *                that is being generated in the case of a mirror class.
     *  @return       An option that is:
     *                - defined and contains an AnnotationInfo of the ScalaSignature type,
     *                  instantiated with the pickle signature for sym.
     *                - empty if the jclass/sym pair must not contain a pickle.
     *
     */
    def getAnnotPickle(jclassName: String, sym: Symbol): Option[AnnotationInfo] = {
      currentRun.symData get sym match {
        case Some(pickle) if !nme.isModuleName(newTermName(jclassName)) =>
          val scalaAnnot = {
            val sigBytes = ScalaSigBytes(pickle.bytes.take(pickle.writeIndex))
            AnnotationInfo(sigBytes.sigAnnot, Nil, List((nme.bytes, sigBytes)))
          }
          pickledBytes += pickle.writeIndex
          currentRun.symData -= sym
          currentRun.symData -= sym.companionSymbol
          Some(scalaAnnot)
        case _ =>
          None
      }
    }

  }

}