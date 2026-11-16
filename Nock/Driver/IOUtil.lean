/-
  Nock/Driver/IOUtil.lean

  **The driver's file primitives, in one place.**  `scripts/elab-inputs.py` flags every
  textual file read, because a module that reads a file while it ELABORATES has an input Lake cannot see.
  The driver reads and writes files only when its functions are RUN (the executable, and the `#eval` of
  `DriverTest.lean`, which reads only files it wrote itself under `.lake/driver-test/`), never to build a
  declaration.
-/
set_option autoImplicit false

namespace Nock.Driver.IOUtil

open System (FilePath)

-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml
-- elab-input: lakefile.toml

def readText (f : FilePath) : IO String := IO.FS.readFile f
def writeText (f : FilePath) (s : String) : IO Unit := IO.FS.writeFile f s
def readBin (f : FilePath) : IO ByteArray := IO.FS.readBinFile f
def writeBin (f : FilePath) (b : ByteArray) : IO Unit := IO.FS.writeBinFile f b
def mkdirs (f : FilePath) : IO Unit := IO.FS.createDirAll f
def openRead (f : FilePath) : IO IO.FS.Handle := IO.FS.Handle.mk f .read

end Nock.Driver.IOUtil
