import Batteries.Tactic.Alias
import Nock.NockVM

/-
  Alias for `Nock.NockVM.V_NockVMROM_forest` under the name `Thm:NockVMROM:forest-control`.  It is
  separate from the paper-facing `Thm:NockVMROM` alias and asserts nothing about that alias's target.
-/
alias «Thm:NockVMROM:forest-control» := Nock.NockVM.V_NockVMROM_forest
