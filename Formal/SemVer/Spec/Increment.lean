import SemVer.Spec.Precedence

/-!
# Semantic Versioning 2.0.0 — バージョンの繰り上げ(§6〜§8)

出典: <https://semver.org/spec/v2.0.0.html>(CC BY 3.0)

このファイルは信頼の基点である。

仕様が定めるのは、通常バージョンから次のリリースを出すときにどの数値を上げ、どれを 0 に戻すかである。
プレリリース版に対する「繰り上げ」という操作は仕様にない。そこでこのライブラリは、
繰り上げを §11 の優先順位だけを使って次のように定める(node-semver の `inc` と同じ結果になる)。

* パッチの繰り上げ: 元より高い通常バージョンのうち、優先順位が最も低いもの。
* マイナーの繰り上げ: 元より高く、パッチが 0 である通常バージョンのうち、最も低いもの。
* メジャーの繰り上げ: 元より高く、マイナーとパッチが 0 である通常バージョンのうち、最も低いもの。

通常バージョンに対しては、これは §6〜§8 の「数値を 1 上げて下位を 0 に戻す」と一致する。
プレリリース版に対しては、対応する通常バージョン(§9)が条件を満たせばそれになる。
たとえば `1.2.3-rc.1` のパッチの繰り上げは `1.2.3`、`1.2.0-rc.1` のマイナーの繰り上げは `1.2.0`。

`nextPatch` などの関数がこの条件を満たすことは `SemVer.Theorems.Increment` で証明する。
-/

namespace SemVer.Spec

/-- 通常バージョン(プレリリース版でない)。 -/
def Version.IsNormal (v : Version) : Prop := v.preRelease = []

/-- パッチの繰り上げ先になりうるバージョン: 通常バージョン(§6)。 -/
def Version.IsPatchRelease (v : Version) : Prop := v.IsNormal

/-- マイナーの繰り上げ先になりうるバージョン: パッチが 0 の通常バージョン(§7)。 -/
def Version.IsMinorRelease (v : Version) : Prop := v.IsNormal ∧ v.patch = 0

/-- メジャーの繰り上げ先になりうるバージョン: マイナーとパッチが 0 の通常バージョン(§8)。 -/
def Version.IsMajorRelease (v : Version) : Prop := v.IsNormal ∧ v.minor = 0 ∧ v.patch = 0

/-- `w` は、`P` を満たし `v` より優先順位が高いバージョンのうち、優先順位が最も低い。 -/
def IsLeastAbove (P : Version → Prop) (v w : Version) : Prop :=
  P w ∧ v.Lt w ∧ ∀ u, P u → v.Lt u → ¬ u.Lt w

/-- パッチの繰り上げ。結果にビルドメタデータは付けない。 -/
def Version.nextPatch (v : Version) : Version :=
  if v.preRelease = [] then
    { major := v.major, minor := v.minor, patch := v.patch + 1 }
  else
    { major := v.major, minor := v.minor, patch := v.patch }

/-- マイナーの繰り上げ。 -/
def Version.nextMinor (v : Version) : Version :=
  if v.patch ≠ 0 ∨ v.preRelease = [] then
    { major := v.major, minor := v.minor + 1, patch := 0 }
  else
    { major := v.major, minor := v.minor, patch := 0 }

/-- メジャーの繰り上げ。 -/
def Version.nextMajor (v : Version) : Version :=
  if v.minor ≠ 0 ∨ v.patch ≠ 0 ∨ v.preRelease = [] then
    { major := v.major + 1, minor := 0, patch := 0 }
  else
    { major := v.major, minor := 0, patch := 0 }

end SemVer.Spec
