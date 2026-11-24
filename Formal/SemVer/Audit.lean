import SemVer.Theorems.Increment
import SemVer.Parser.Version
import SemVer.Model.Correctness

/-!
# 公理の監査

主要な定理が依存する公理を固定する。`sorryAx` や想定外の公理が混入すると、
出力が下の期待と食い違ってビルドが失敗する。

`propext`、`Classical.choice`、`Quot.sound` は Lean の標準の公理で、`simp`、`omega`、`by_cases` が使う。
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

/-! ## 文法と文字列の対応 -/

/-- info: 'SemVer.validSemVer_iff_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validSemVer_iff_components

/-- info: 'SemVer.parse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_sound

/-- info: 'SemVer.parse_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_complete

/-- info: 'SemVer.validSemVer_iff_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validSemVer_iff_parse

/-- info: 'SemVer.parseVersion_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parseVersion_sound

/-- info: 'SemVer.parseVersion_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parseVersion_complete

/-- info: 'SemVer.validSemVer_iff_parseVersion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validSemVer_iff_parseVersion

/-- info: 'SemVer.validSemVer_iff_version' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validSemVer_iff_version

/--
info: 'SemVer.Spec.Components.render_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Components.render_injective

/--
info: 'SemVer.Spec.Version.render_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Version.render_injective

/--
info: 'SemVer.Spec.Components.WF.toComponents_toVersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Components.WF.toComponents_toVersion

/--
info: 'SemVer.Spec.Version.WF.toVersion_toComponents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Version.WF.toVersion_toComponents

/-! ## 実装モデル -/

/-- info: 'SemVer.numericLt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numericLt_iff

/--
info: 'SemVer.Spec.Components.lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Components.lt_iff

/--
info: 'SemVer.Spec.Components.precedenceEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Components.precedenceEq_iff

/--
info: 'SemVer.Spec.Components.lt_trichotomous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Components.lt_trichotomous
