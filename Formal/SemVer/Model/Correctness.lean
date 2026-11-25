import SemVer.Model.Precedence
import SemVer.Theorems.Denotation
import SemVer.Theorems.Precedence

/-!
# 実装モデルの正しさ

バイト列のままの比較が、仕様の優先順位と一致することを示す。

主定理:

* `numericLt_iff`: 数値識別子の「桁数、次に辞書順」の比較は、数値の大小と一致する。
* `Components.lt_iff`: 妥当な構成要素について、`Components.Lt` は `Version.Lt` と一致する。
* `Components.precedenceEq_iff`: 同じく、優先順位の等しさも一致する。

これにより、§11 について証明した性質(全順序であることなど)がそのまま構成要素の比較にも成り立つ。
-/

namespace SemVer

open Spec

/-! ## 数字列の値の比較 -/

/-- 同じ桁数の数字列を読み進めるとき、途中の値に差があれば最後まで逆転しない。 -/
theorem foldl_decimalStep_lt_of_lt : ∀ (a b : List Byte), a.length = b.length →
    (∀ c ∈ a, IsDigit c) → ∀ acc₁ acc₂ : Nat, acc₁ < acc₂ →
    a.foldl decimalStep acc₁ < b.foldl decimalStep acc₂
  | [], [], _, _, _, _, h => h
  | [], _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | c₁ :: a, c₂ :: b, hlen, ha, acc₁, acc₂, h => by
    have h₁ := (ha c₁ (by simp)).digitValue_lt
    exact foldl_decimalStep_lt_of_lt a b (by simpa using hlen)
      (fun c hc => ha c (List.mem_cons_of_mem _ hc)) _ _
      (by unfold decimalStep; omega)

/-- 同じ桁数の数字列は、辞書順で小さければ値も小さい。 -/
theorem foldl_decimalStep_lt_of_lexLt : ∀ (a b : List Byte), a.length = b.length →
    (∀ c ∈ a, IsDigit c) → LexLt AsciiLt a b →
    ∀ acc : Nat, a.foldl decimalStep acc < b.foldl decimalStep acc
  | [], [], _, _, h, _ => absurd h LexLt.nil_nil
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | c₁ :: a, c₂ :: b, hlen, ha, h, acc => by
    have hlen' : a.length = b.length := by simpa using hlen
    have ha' : ∀ c ∈ a, IsDigit c := fun c hc => ha c (List.mem_cons_of_mem _ hc)
    have hb₁ := (ha c₁ (by simp)).toNat_bounds
    rcases LexLt.cons_cons.mp h with hlt | ⟨heq, hrest⟩
    · have hlt' : c₁.toNat < c₂.toNat := hlt
      have e : Ascii.zero.toNat = 48 := rfl
      exact foldl_decimalStep_lt_of_lt a b hlen' ha' _ _
        (by unfold decimalStep digitValue; omega)
    · subst heq
      exact foldl_decimalStep_lt_of_lexLt a b hlen' ha' hrest _

/-- 先頭にゼロを補っても値は変わらない。 -/
theorem foldl_decimalStep_replicate_zero (k : Nat) (a : List Byte) :
    (List.replicate k Ascii.zero ++ a).foldl decimalStep 0 = a.foldl decimalStep 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : decimalStep 0 Ascii.zero = 0 := by decide
    rw [List.replicate_succ, List.cons_append, List.foldl_cons, e, ih]

/-- 数値識別子は、桁数が少なければ値も小さい。 -/
theorem decimalValue_lt_of_length_lt {a b : List Byte}
    (ha : NumericIdentifier a) (hb : NumericIdentifier b) (hlen : a.length < b.length) :
    decimalValue a < decimalValue b := by
  have haAll := ha.forall_isDigit
  have haLen : 0 < a.length := List.length_pos_iff.mpr ha.ne_nil
  -- `b` は 2 桁以上なので、先頭は 0 でない
  obtain ⟨d, ds, rfl, hd⟩ : ∃ d ds, b = d :: ds ∧ IsPositiveDigit d := by
    cases hb with
    | zero =>
      have h1 : [Ascii.zero].length = 1 := rfl
      omega
    | positive hd => exact ⟨_, [], rfl, hd⟩
    | positiveDigits hd _ => exact ⟨_, _, rfl, hd⟩
  obtain ⟨j, hj⟩ : ∃ j, (d :: ds).length = a.length + (j + 1) :=
    ⟨(d :: ds).length - a.length - 1, by omega⟩
  -- `a` の先頭にゼロを補って `b` と同じ桁数にする
  have hpadLen : (List.replicate (j + 1) Ascii.zero ++ a).length = (d :: ds).length := by
    rw [List.length_append, List.length_replicate]
    omega
  have hpadAll : ∀ c ∈ List.replicate (j + 1) Ascii.zero ++ a, IsDigit c := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.eq_of_mem_replicate hc]
      exact Or.inl rfl
    · exact haAll c hc
  have hzd : AsciiLt Ascii.zero d := by
    obtain ⟨h₁, _⟩ := hd
    have h₁' := UInt8.le_iff_toNat_le.mp h₁
    have e₁ : (0x31 : UInt8).toNat = 49 := rfl
    have e : Ascii.zero.toNat = 48 := rfl
    show Ascii.zero.toNat < d.toNat
    omega
  have hlex : LexLt AsciiLt (List.replicate (j + 1) Ascii.zero ++ a) (d :: ds) := by
    show LexLt AsciiLt (Ascii.zero :: (List.replicate j Ascii.zero ++ a)) (d :: ds)
    exact LexLt.cons_cons.mpr (Or.inl hzd)
  have hlt := foldl_decimalStep_lt_of_lexLt _ _ hpadLen hpadAll hlex 0
  rw [foldl_decimalStep_replicate_zero] at hlt
  exact hlt

/-! ## 数値識別子の比較 -/

theorem NumericLt.trichotomous (a b : List Byte) : NumericLt a b ∨ a = b ∨ NumericLt b a := by
  rcases Nat.lt_trichotomy a.length b.length with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases LexLt.trichotomous asciiLt_strictTotalOrder.trichotomous a b with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem NumericLt.decimalValue_lt {a b : List Byte}
    (ha : NumericIdentifier a) (hb : NumericIdentifier b) (h : NumericLt a b) :
    decimalValue a < decimalValue b := by
  rcases h with h | ⟨hlen, hlex⟩
  · exact decimalValue_lt_of_length_lt ha hb h
  · exact foldl_decimalStep_lt_of_lexLt a b hlen ha.forall_isDigit hlex 0

/-- 数値識別子の「桁数、次に辞書順」の比較は、数値の大小と一致する。 -/
theorem numericLt_iff {a b : List Byte} (ha : NumericIdentifier a) (hb : NumericIdentifier b) :
    NumericLt a b ↔ decimalValue a < decimalValue b := by
  constructor
  · exact NumericLt.decimalValue_lt ha hb
  · intro h
    rcases NumericLt.trichotomous a b with h' | h' | h'
    · exact h'
    · subst h'
      exact absurd h (Nat.lt_irrefl _)
    · exact absurd (NumericLt.decimalValue_lt hb ha h') (Nat.lt_asymm h)

/-- 数値識別子は、値が等しければバイト列として等しい。 -/
theorem decimalValue_inj {a b : List Byte} (ha : NumericIdentifier a) (hb : NumericIdentifier b) :
    decimalValue a = decimalValue b ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg decimalDigits h
    rwa [ha.decimalDigits_decimalValue, hb.decimalDigits_decimalValue] at h'
  · intro h
    rw [h]

/-! ## プレリリース識別子の比較 -/

theorem ofBytes_inj {a b : List Byte} (ha : PreReleaseIdentifier a) (hb : PreReleaseIdentifier b) :
    a = b ↔ PreReleaseId.ofBytes a = PreReleaseId.ofBytes b := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg PreReleaseId.toBytes h
    rwa [ha.toBytes_ofBytes, hb.toBytes_ofBytes] at h'

/-- プレリリース識別子のバイト列のままの比較は、§11.4.1〜§11.4.3 の比較と一致する。 -/
theorem identifierLt_iff {a b : List Byte}
    (ha : PreReleaseIdentifier a) (hb : PreReleaseIdentifier b) :
    IdentifierLt a b ↔ (PreReleaseId.ofBytes a).Lt (PreReleaseId.ofBytes b) := by
  unfold IdentifierLt
  cases ha with
  | numeric ha =>
    cases hb with
    | numeric hb =>
      rw [PreReleaseId.ofBytes_of_digits ha.forall_isDigit,
        PreReleaseId.ofBytes_of_digits hb.forall_isDigit,
        ite_eq_left ha.forall_isDigit, ite_eq_left hb.forall_isDigit]
      exact numericLt_iff ha hb
    | alphanumeric hb =>
      rw [PreReleaseId.ofBytes_of_digits ha.forall_isDigit,
        PreReleaseId.ofBytes_of_not_digits hb.not_forall_isDigit,
        ite_eq_left ha.forall_isDigit, ite_eq_right hb.not_forall_isDigit]
      exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | alphanumeric ha =>
    cases hb with
    | numeric hb =>
      rw [PreReleaseId.ofBytes_of_not_digits ha.not_forall_isDigit,
        PreReleaseId.ofBytes_of_digits hb.forall_isDigit,
        ite_eq_right ha.not_forall_isDigit, ite_eq_left hb.forall_isDigit]
      exact Iff.rfl
    | alphanumeric hb =>
      rw [PreReleaseId.ofBytes_of_not_digits ha.not_forall_isDigit,
        PreReleaseId.ofBytes_of_not_digits hb.not_forall_isDigit,
        ite_eq_right ha.not_forall_isDigit, ite_eq_right hb.not_forall_isDigit]
      exact Iff.rfl

/-- プレリリース識別子の列のバイト列のままの比較は、§11.3〜§11.4 の比較と一致する。 -/
theorem preReleaseBytesLt_iff : ∀ {p q : List (List Byte)},
    (∀ i ∈ p, PreReleaseIdentifier i) → (∀ i ∈ q, PreReleaseIdentifier i) →
    (PreReleaseBytesLt p q ↔
      PreReleaseLt (p.map PreReleaseId.ofBytes) (q.map PreReleaseId.ofBytes))
  | [], _, _, _ => Iff.rfl
  | _ :: _, [], _, _ => Iff.rfl
  | a :: as, b :: bs, hp, hq =>
    LexLt.map_iff (a :: as) (b :: bs)
      (fun x hx y hy => identifierLt_iff (hp x hx) (hq y hy))
      (fun x hx y hy => ofBytes_inj (hp x hx) (hq y hy))

theorem map_ofBytes_inj {p q : List (List Byte)}
    (hp : ∀ i ∈ p, PreReleaseIdentifier i) (hq : ∀ i ∈ q, PreReleaseIdentifier i) :
    p = q ↔ p.map PreReleaseId.ofBytes = q.map PreReleaseId.ofBytes := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (List.map PreReleaseId.toBytes) h
    rwa [map_map_eq_self p (fun i hi => (hp i hi).toBytes_ofBytes),
      map_map_eq_self q (fun i hi => (hq i hi).toBytes_ofBytes)] at h'

/-! ## 構成要素全体 -/

/-- 妥当な構成要素について、バイト列のままの優先順位は §11 の優先順位と一致する。 -/
theorem Spec.Components.lt_iff {c d : Components} (hc : c.WF) (hd : d.WF) :
    c.Lt d ↔ c.toVersion.Lt d.toVersion := by
  unfold Components.Lt Version.Lt
  exact
    or_congr (numericLt_iff hc.major hd.major)
      (and_congr (decimalValue_inj hc.major hd.major).symm
        (or_congr (numericLt_iff hc.minor hd.minor)
          (and_congr (decimalValue_inj hc.minor hd.minor).symm
            (or_congr (numericLt_iff hc.patch hd.patch)
              (and_congr (decimalValue_inj hc.patch hd.patch).symm
                (preReleaseBytesLt_iff hc.preRelease hd.preRelease))))))

/-- 妥当な構成要素について、優先順位の等しさも §11 と一致する。 -/
theorem Spec.Components.precedenceEq_iff {c d : Components} (hc : c.WF) (hd : d.WF) :
    c.PrecedenceEq d ↔ c.toVersion.PrecedenceEq d.toVersion := by
  unfold Components.PrecedenceEq Version.PrecedenceEq
  exact
    and_congr (decimalValue_inj hc.major hd.major).symm
      (and_congr (decimalValue_inj hc.minor hd.minor).symm
        (and_congr (decimalValue_inj hc.patch hd.patch).symm
          (map_ofBytes_inj hc.preRelease hd.preRelease)))

/-! ## 構成要素の比較が満たす性質 -/

/-- 任意の 2 つの妥当な構成要素は、どちらかが低いか、優先順位が等しい。 -/
theorem Spec.Components.lt_trichotomous {c d : Components} (hc : c.WF) (hd : d.WF) :
    c.Lt d ∨ c.PrecedenceEq d ∨ d.Lt c := by
  rcases Version.Lt.trichotomous c.toVersion d.toVersion with h | h | h
  · exact Or.inl ((Components.lt_iff hc hd).mpr h)
  · exact Or.inr (Or.inl ((Components.precedenceEq_iff hc hd).mpr h))
  · exact Or.inr (Or.inr ((Components.lt_iff hd hc).mpr h))

theorem Spec.Components.lt_irrefl {c : Components} (hc : c.WF) : ¬ c.Lt c :=
  fun h => Version.Lt.irrefl _ ((Components.lt_iff hc hc).mp h)

theorem Spec.Components.lt_trans {c d e : Components} (hc : c.WF) (hd : d.WF) (he : e.WF)
    (h₁ : c.Lt d) (h₂ : d.Lt e) : c.Lt e :=
  (Components.lt_iff hc he).mpr
    (Version.Lt.trans ((Components.lt_iff hc hd).mp h₁) ((Components.lt_iff hd he).mp h₂))

theorem Spec.Components.lt_asymm {c d : Components} (hc : c.WF) (hd : d.WF) (h : c.Lt d) :
    ¬ d.Lt c :=
  fun h' => Version.Lt.asymm ((Components.lt_iff hc hd).mp h) ((Components.lt_iff hd hc).mp h')

theorem Spec.Components.not_lt_of_precedenceEq {c d : Components} (hc : c.WF) (hd : d.WF)
    (h : c.PrecedenceEq d) : ¬ c.Lt d :=
  fun h' => Version.PrecedenceEq.not_lt ((Components.precedenceEq_iff hc hd).mp h)
    ((Components.lt_iff hc hd).mp h')

end SemVer
