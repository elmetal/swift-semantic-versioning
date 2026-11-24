import SemVer.Spec.Grammar

/-!
# Semantic Versioning 2.0.0 — 抽象的なバージョンと優先順位(§11)

出典: <https://semver.org/spec/v2.0.0.html>(CC BY 3.0)

このファイルは信頼の基点である。バージョンを文字列ではなく値として表し、§11 の優先順位を
条項ごとに定義する。X, Y, Z と数値プレリリース識別子は仕様どおり上限のない非負整数(`Nat`)で持つ。

抽象値が文法上妥当であること(英数字識別子の中身など)と、文字列との対応は別ファイルで定める。
-/

namespace SemVer.Spec

/-- プレリリース識別子(§9)。 -/
inductive PreReleaseId where
  /-- 数字だけからなる識別子。値は非負整数。 -/
  | numeric (value : Nat)
  /-- 英字またはハイフンを含む識別子。ASCII バイト列。 -/
  | alphanumeric (bytes : List Byte)
  deriving DecidableEq, Repr

/-- バージョン(§2, §9, §10)。 -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  /-- プレリリース識別子の列。空なら通常バージョン。 -/
  preRelease : List PreReleaseId := []
  /-- ビルドメタデータ識別子の列。 -/
  build : List (List Byte) := []
  deriving DecidableEq, Repr

/--
左から順に比べて最初の相違で決まる辞書式順序。
先行する要素がすべて等しければ、短い列の方が小さい。
§11.4.2(ASCII 順)と §11.4 / §11.4.4(識別子列の比較)の両方で使う。
-/
def LexLt {α : Type} (lt : α → α → Prop) : List α → List α → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => lt a b ∨ (a = b ∧ LexLt lt as bs)

/-- ASCII 順。コード値の大小。 -/
def AsciiLt (a b : Byte) : Prop := a.toNat < b.toNat

/-- プレリリース識別子 1 個同士の優先順位(§11.4.1〜§11.4.3)。 -/
def PreReleaseId.Lt : PreReleaseId → PreReleaseId → Prop
  /- §11.4.1: 数字だけの識別子は数値として比べる。 -/
  | .numeric a, .numeric b => a < b
  /- §11.4.2: 英字やハイフンを含む識別子は ASCII 順で辞書式に比べる。 -/
  | .alphanumeric a, .alphanumeric b => LexLt AsciiLt a b
  /- §11.4.3: 数値識別子は非数値識別子より常に低い。 -/
  | .numeric _, .alphanumeric _ => True
  | .alphanumeric _, .numeric _ => False

/-- major, minor, patch が等しい 2 つのバージョンの、プレリリース部分による優先順位。 -/
def PreReleaseLt : List PreReleaseId → List PreReleaseId → Prop
  /- §11.3: 通常バージョンは、同じ major.minor.patch のどのバージョンよりも低くない。 -/
  | [], _ => False
  /- §11.3: プレリリース版は通常バージョンより低い。 -/
  | _ :: _, [] => True
  /- §11.4, §11.4.4: 識別子を左から比べる。すべて等しければ識別子が多い方が高い。 -/
  | a :: as, b :: bs => LexLt PreReleaseId.Lt (a :: as) (b :: bs)

/--
優先順位(§11)。`v.Lt w` は「`v` の優先順位が `w` より低い」。

§11.1: major, minor, patch, プレリリースの順に分けて比べ、ビルドメタデータは使わない。
§11.2: 最初の相違で決まり、major, minor, patch は数値として比べる。
-/
def Version.Lt (v w : Version) : Prop :=
  v.major < w.major ∨ (v.major = w.major ∧
    (v.minor < w.minor ∨ (v.minor = w.minor ∧
      (v.patch < w.patch ∨ (v.patch = w.patch ∧
        PreReleaseLt v.preRelease w.preRelease)))))

/-- 優先順位が等しい。ビルドメタデータ以外がすべて一致する(§10, §11.1)。 -/
def Version.PrecedenceEq (v w : Version) : Prop :=
  v.major = w.major ∧ v.minor = w.minor ∧ v.patch = w.patch ∧ v.preRelease = w.preRelease

end SemVer.Spec
