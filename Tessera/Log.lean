/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Tessera.Text

/-! # Logs

A log is read later in a terminal, with `cat` or `tail -f`, by tools that do not filter what
they print. So a `Log` takes only `Text`, which holds nothing a terminal would act on, and its
file is readable by its owner only. -/

namespace Tessera

structure Log where
  private mk ::
  handle : IO.FS.Handle

/-- Open the log at `path` to add to it, made readable and writable by its owner only before
anything is written to it. -/
def Log.open (path : System.FilePath) : IO Log := do
  let handle ← IO.FS.Handle.mk path .append
  IO.setAccessRights path { user := { read := true, write := true } }
  return ⟨handle⟩

/-- Add a line to the log. -/
def Log.write {cs : Charset} {o : Origin} (l : Log) (t : Text cs o) : IO Unit := do
  l.handle.putStrLn t.text
  l.handle.flush

end Tessera
