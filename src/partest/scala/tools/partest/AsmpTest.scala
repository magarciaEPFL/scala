/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 */

package scala.tools.partest

import scala.tools.nsc._
import nest.FileUtil._
import io.Directory

/** A trait for testing a javap-like view of bytecode,
 *  a view produced by ASM's Textifier in .asmp textual files, one for each .class file.
 *  Example:
 *  {{{
 *    object Test extends AsmpTest
 *  }}}
 */
abstract class AsmpTest extends DirectTest {
  // override to use source code other than the file being tested.
  def code = testPath.slurp()

  override def extraSettings: String = "-usejavacp "

  // Compile, read in all the *.asmp files, delete them, and return their contents
  def collectAsmp(args: String*): List[String] = {
    compile("-d" :: testOutput.path :: args.toList : _*)
    val textFiles = testOutput.files.toList filter (_ hasExtension "asmp")

    try     textFiles sortBy (_.name) flatMap (f => f.lines.toList)
    finally textFiles foreach (f => f.delete())
  }

  // Default show() compiles the code and concatenates all of their javap-like representation.
  // Comments hint at an alternative realization: run with optimization on and off, and show their diff.
  def show() {
    val lines1 = collectAsmp("-target:jvm-1.6", "-Ygen-asmp") // 1.6 target chosen just to activate GenASM
    // val lines2 = collectIcode("-optimise")

    // println(compareContents(lines1, lines2))
    println(lines1)
  }
}
