
import Smt

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Real

theorem Example_1 {a b c : ℝ} : 0 ≥ a := by
  smt_only

theorem Example_2 {a b c : Real} : 0 ≤ Real.sqrt b := by
  smt_only

theorem Example_3 {a b c : Real} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  smt_only
