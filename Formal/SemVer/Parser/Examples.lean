import SemVer.Parser.Version
import SemVer.Spec.Decidable

/-!
# 文法の例による点検

`ValidSemVer`(BNF の直訳)を、妥当な文字列と妥当でない文字列の両方で評価する。
判定は `validSemVer_iff_parse` で BNF と同値だと証明済みの手続きで行うので、
ここでの結果は BNF そのものについての事実である。期待と違えばビルドが失敗する。
-/

namespace SemVer.Parser.Examples

open Spec

private def bytes (s : String) : List Byte := s.toUTF8.toList

private def valid (s : String) : Bool := decide (ValidSemVer (bytes s))

/-! ## 妥当な文字列 -/

private def validExamples : List String := [
  "0.0.0",
  "0.0.4",
  "1.2.3",
  "10.20.30",
  "1.0.0",
  "2.0.0",
  "1.1.7",
  "1.1.2-prerelease+meta",
  "1.1.2+meta",
  "1.1.2+meta-valid",
  "1.0.0-alpha",
  "1.0.0-beta",
  "1.0.0-alpha.beta",
  "1.0.0-alpha.beta.1",
  "1.0.0-alpha.1",
  "1.0.0-alpha0.valid",
  "1.0.0-alpha.0valid",
  "1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay",
  "1.0.0-rc.1+build.1",
  "2.0.0-rc.1+build.123",
  "1.2.3-beta",
  "10.2.3-DEV-SNAPSHOT",
  "1.2.3-SNAPSHOT-123",
  "2.0.0+build.1848",
  "2.0.1-alpha.1227",
  "1.0.0-alpha+beta",
  "1.2.3----RC-SNAPSHOT.12.9.1--.12+788",
  "1.2.3----R-S.12.9.1--.12+meta",
  "1.2.3----RC-SNAPSHOT.12.9.1--.12",
  "1.0.0+0.build.1-rc.10000aaa-kk-0.1",
  "99999999999999999999999.999999999999999999.99999999999999999",
  "1.0.0-0A.is.legal",
  -- 仕様書 §9, §10 の例
  "1.0.0-0.3.7",
  "1.0.0-x.7.z.92",
  "1.0.0-x-y-z.--",
  "1.0.0-alpha+001",
  "1.0.0+20130313144700",
  "1.0.0-beta+exp.sha.5114f85",
  "1.0.0+21AF26D3----117B344092BD",
  -- 境界
  "1.0.0--",
  "1.0.0-0",
  "1.0.0-0a",
  "1.0.0-a0",
  "1.0.0+0",
  "1.0.0+00",
  "1.0.0+-",
  "1.0.0-a+-"
]

#guard validExamples.all valid

/-! ## 妥当でない文字列 -/

private def invalidExamples : List String := [
  "",
  "1",
  "1.2",
  "1.2.3.4",
  "1.2.3-0123",
  "1.2.3-0123.0123",
  "1.1.2+.123",
  "+invalid",
  "-invalid",
  "-invalid+invalid",
  "-invalid.01",
  "alpha",
  "alpha.beta",
  "alpha.beta.1",
  "alpha.1",
  "alpha+beta",
  "alpha_beta",
  "alpha.",
  "alpha..",
  "beta",
  "1.0.0-alpha_beta",
  "-alpha.",
  "1.0.0-alpha..",
  "1.0.0-alpha..1",
  "1.0.0-alpha...1",
  "01.1.1",
  "1.01.1",
  "1.1.01",
  "1.2.3.DEV",
  "1.2-SNAPSHOT",
  "1.2.31.2.3----RC-SNAPSHOT.12.09.1--..12+788",
  "1.2-RC-SNAPSHOT",
  "-1.0.3-gamma+b7718",
  "+justmeta",
  "9.8.7+meta+meta",
  "9.8.7-whatever+meta+meta",
  -- 境界
  "1.0.0-",
  "1.0.0+",
  "1.0.0-+",
  "1.0.0-a+",
  "1.0.0-.a",
  "1.0.0-a.",
  "1.0.0-00",
  "1.0.0-01",
  "1.0.0+a..b",
  ".0.0",
  "1..0",
  "1.0.",
  "00.0.0",
  "v1.0.0",
  "1.0.0 ",
  " 1.0.0",
  "1.0.0\n",
  "1.0.0-a b",
  "1.0.0-a/b",
  "1,0,0",
  -- ASCII 以外(UTF-8 のバイト列として見て妥当でない)
  "１.0.0",
  "1.0.0-é",
  "1.0.0-α",
  "1.0.0+ビルド"
]

#guard invalidExamples.all (fun s => !valid s)

/-! ## 分解結果 -/

#guard parse (bytes "1.2.3-rc.1+build.5") = some {
  major := bytes "1", minor := bytes "2", patch := bytes "3"
  preRelease := [bytes "rc", bytes "1"]
  build := [bytes "build", bytes "5"] }

#guard parse (bytes "10.0.20") = some {
  major := bytes "10", minor := bytes "0", patch := bytes "20"
  preRelease := [], build := [] }

#guard (parse (bytes "1.0.0-x-y-z.--")).map (·.preRelease) = some [bytes "x-y-z", bytes "--"]

/-! ## 文字列から抽象的なバージョンへ -/

#guard parseVersion (bytes "1.2.3-rc.1+build.5") = some {
  major := 1, minor := 2, patch := 3
  preRelease := [.alphanumeric (bytes "rc"), .numeric 1]
  build := [bytes "build", bytes "5"] }

/- 数値に上限はない。 -/
#guard (parseVersion (bytes "99999999999999999999999.0.0")).map (·.major)
  = some 99999999999999999999999

/- `0a` は数字だけではないので英数字識別子、`0` は数値識別子。 -/
#guard (parseVersion (bytes "1.0.0-0a.0")).map (·.preRelease)
  = some [.alphanumeric (bytes "0a"), .numeric 0]

/- 妥当な文字列は、読んでから文字列に戻すと元に戻る。妥当でない文字列は読めない。 -/
#guard validExamples.all fun s => (parseVersion (bytes s)).map Version.render = some (bytes s)
#guard invalidExamples.all fun s => parseVersion (bytes s) = none

/-! ## 優先順位(§11)を文字列のまま検査 -/

private def lt (a b : String) : Bool :=
  match parseVersion (bytes a), parseVersion (bytes b) with
  | some x, some y => decide (x.Lt y)
  | _, _ => false

private def increasing : List String → Bool
  | [] => true
  | x :: xs => xs.all (fun y => lt x y && !lt y x) && increasing xs

#guard increasing ["1.0.0", "2.0.0", "2.1.0", "2.1.1"]

#guard increasing [
  "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta",
  "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"]

/- 桁数が違っても数値として比べる(文字列の辞書順ではない)。 -/
#guard increasing ["1.9.0", "1.10.0", "1.11.0", "2.0.0", "10.0.0"]
#guard increasing ["1.0.0-2", "1.0.0-10", "1.0.0-a", "1.0.0-a.2", "1.0.0-a.10"]

/- ビルドメタデータだけが違う文字列に上下はない。 -/
#guard !lt "1.0.0+a" "1.0.0+b" && !lt "1.0.0+b" "1.0.0+a"

end SemVer.Parser.Examples
