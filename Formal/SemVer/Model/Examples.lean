import SemVer.Model.Correctness
import SemVer.Model.IncrementCorrectness
import SemVer.Parser.Correctness

/-!
# 実装モデルの例による点検

バイト列のままの比較を具体例で評価する。仕様の優先順位との一致は証明済みなので、
ここでは定義が実際に計算できることと、結果が直感どおりであることを確かめる。
-/

namespace SemVer.Model.Examples

open Spec

private def bytes (s : String) : List Byte := s.toUTF8.toList

private def lt (a b : String) : Bool :=
  match parse (bytes a), parse (bytes b) with
  | some c, some d => decide (c.Lt d)
  | _, _ => false

private def increasing : List String → Bool
  | [] => true
  | x :: xs => xs.all (fun y => lt x y && !lt y x) && increasing xs

/- §11.2 と §11.4 の例 -/
#guard increasing ["1.0.0", "2.0.0", "2.1.0", "2.1.1"]

#guard increasing [
  "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
  "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"]

/- 桁数が違っても数値として比べる。 -/
#guard increasing ["1.9.0", "1.10.0", "1.11.0", "2.0.0", "10.0.0"]
#guard increasing ["1.0.0-2", "1.0.0-10", "1.0.0-a", "1.0.0-a.2", "1.0.0-a.10"]

/- 整数型に収まらない桁数でも比べられる。 -/
#guard increasing [
  "18446744073709551615.0.0",
  "18446744073709551616.0.0",
  "99999999999999999999999.0.0",
  "100000000000000000000000.0.0"]

/- ビルドメタデータだけが違う文字列に上下はなく、優先順位が等しい。 -/
#guard !lt "1.0.0+a" "1.0.0+b" && !lt "1.0.0+b" "1.0.0+a"
#guard
  match parse (bytes "1.0.0-rc.1+a"), parse (bytes "1.0.0-rc.1+b.c") with
  | some c, some d => decide (c.PrecedenceEq d) && c != d
  | _, _ => false

/-! ## 仕様の優先順位と同じ結果になること -/

private def samples : List String := [
  "0.0.0", "0.0.1", "0.1.0", "1.0.0", "1.0.1", "1.1.0", "1.9.0", "1.10.0", "2.0.0", "10.0.0",
  "1.0.0-0", "1.0.0-1", "1.0.0-9", "1.0.0-10", "1.0.0-0a", "1.0.0-a", "1.0.0-A", "1.0.0--",
  "1.0.0-a.0", "1.0.0-a.a", "1.0.0-a.b.c", "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta",
  "1.0.0-beta", "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0+build", "1.0.0-rc.1+build",
  "99999999999999999999999.0.0", "1.0.0-99999999999999999999999"]

private def agree (a b : String) : Bool :=
  match parse (bytes a), parse (bytes b) with
  | some c, some d =>
    decide (c.Lt d) == decide (c.toVersion.Lt d.toVersion) &&
      decide (c.PrecedenceEq d) == decide (c.toVersion.PrecedenceEq d.toVersion)
  | _, _ => false

#guard samples.all fun a => samples.all fun b => agree a b

/-! ## 繰り上げ -/

private def next (f : Components → Components) (s : String) : Option String :=
  (parse (bytes s)).map fun c => String.ofList ((f c).render.map fun b => Char.ofNat b.toNat)

#guard next Components.nextPatch "1.2.3" = some "1.2.4"
#guard next Components.nextPatch "1.2.9" = some "1.2.10"
#guard next Components.nextPatch "1.2.3-rc.1" = some "1.2.3"
#guard next Components.nextPatch "1.2.3+build" = some "1.2.4"
#guard next Components.nextMinor "1.9.3" = some "1.10.0"
#guard next Components.nextMinor "1.2.0-rc.1" = some "1.2.0"
#guard next Components.nextMinor "1.2.3-rc.1" = some "1.3.0"
#guard next Components.nextMajor "9.1.0-rc.1" = some "10.0.0"
#guard next Components.nextMajor "2.0.0-rc.1" = some "2.0.0"
#guard next Components.nextMajor "99.99.99" = some "100.0.0"

/- 整数型に収まらない桁数でも繰り上がる。 -/
#guard next Components.nextPatch "1.2.18446744073709551615" = some "1.2.18446744073709551616"
#guard next Components.nextMajor "99999999999999999999999.0.0"
  = some "100000000000000000000000.0.0"

/- 仕様の繰り上げと同じ結果になる。 -/
#guard samples.all fun s =>
  match parse (bytes s) with
  | some c =>
    c.nextPatch.toVersion = c.toVersion.nextPatch &&
      c.nextMinor.toVersion = c.toVersion.nextMinor &&
      c.nextMajor.toVersion = c.toVersion.nextMajor
  | none => false

end SemVer.Model.Examples
