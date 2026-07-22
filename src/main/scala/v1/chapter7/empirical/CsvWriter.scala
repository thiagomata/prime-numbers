package v1.chapter7.empirical

import stainless.annotation.extern
import java.io.FileWriter
import java.io.File

@extern
object CsvWriter {

  private val header = "k,p,p_next,G_local,delta,extinction"

  def init(path: String): Unit = {
    val file = new File(path)
    file.getParentFile.mkdirs()
    val w = new FileWriter(file)
    w.write(header + "\n")
    w.close()
  }

  def append(path: String, row: OutputRow): Unit = {
    val w = new FileWriter(path, true)
    w.write(s"${row.k},${row.p},${row.pNext},${row.gLocal},${row.delta},${row.extinction}\n")
    w.close()
  }
}
