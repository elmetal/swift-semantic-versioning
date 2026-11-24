import SemVer.Theorems.Increment

/-!
# 公理の監査

主要な定理が依存する公理を固定する。`sorryAx` や想定外の公理が混入すると、
出力が下の期待と食い違ってビルドが失敗する。
-/

open SemVer SemVer.Spec

/-- info: 'SemVer.Spec.LexLt.strictTotalOrder' does not depend on any axioms -/
#guard_msgs in #print axioms LexLt.strictTotalOrder

/-- info: 'SemVer.Spec.Version.Lt.irrefl' does not depend on any axioms -/
#guard_msgs in #print axioms Version.Lt.irrefl

/-- info: 'SemVer.Spec.Version.Lt.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Version.Lt.trans

/-- info: 'SemVer.Spec.Version.Lt.trichotomous' does not depend on any axioms -/
#guard_msgs in #print axioms Version.Lt.trichotomous

/-- info: 'SemVer.Spec.Version.Lt.congr_left' does not depend on any axioms -/
#guard_msgs in #print axioms Version.Lt.congr_left

/-- info: 'SemVer.Spec.Version.Lt.congr_right' does not depend on any axioms -/
#guard_msgs in #print axioms Version.Lt.congr_right

/-- info: 'SemVer.Spec.Version.precedenceEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Version.precedenceEq_iff

/-- info: 'SemVer.Spec.PreReleaseLt.append_right' does not depend on any axioms -/
#guard_msgs in #print axioms PreReleaseLt.append_right

/-- info: 'SemVer.Spec.Version.lt_nextMajor' does not depend on any axioms -/
#guard_msgs in #print axioms Version.lt_nextMajor
