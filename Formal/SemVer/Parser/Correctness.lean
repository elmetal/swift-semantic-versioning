import SemVer.Parser.Components

/-!
# 参照パーサの正しさ

主定理:

* `parse_sound`: `parse` が成功したら、結果は妥当で、文字列に戻すと入力と一致する。
* `parse_complete`: 妥当な構成要素を文字列にして `parse` すると、元の構成要素が得られる。
* `validSemVer_iff_components`: BNF で妥当な文字列とは、妥当な構成要素を文字列にしたものである。
* `validSemVer_iff_parse`: BNF で妥当であることと、`parse` が成功することは同値。

これらを合わせると、妥当な文字列と妥当な構成要素は `parse` と `render` で 1 対 1 に対応する。
-/

namespace SemVer

open Spec

/-! ## 識別子列の分解と連結 -/

theorem joinIdentifiers_parseIdentifiers (o : Option (List Byte)) :
    joinIdentifiers (parseIdentifiers o) = o := by
  cases o with
  | none => rfl
  | some s => simp [parseIdentifiers, joinIdentifiers, join_splitOn]

theorem parseIdentifiers_joinIdentifiers {is : List (List Byte)}
    (h : ∀ i ∈ is, Ascii.dot ∉ i) : parseIdentifiers (joinIdentifiers is) = is := by
  cases is with
  | nil => rfl
  | cons i is =>
    have hsplit := splitOn_join is i (h i (by simp))
      (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp [parseIdentifiers, joinIdentifiers, hsplit]

theorem forall_mem_suffix_joinIdentifiers {q : Byte → Prop} {sep : Byte}
    (hsep : q sep) (hdot : q Ascii.dot) {is : List (List Byte)}
    (h : ∀ i ∈ is, ∀ b ∈ i, q b) : ∀ b ∈ suffix sep (joinIdentifiers is), q b := by
  cases is with
  | nil => simp [suffix, joinIdentifiers]
  | cons i is =>
    intro b hb
    change b ∈ sep :: join Ascii.dot i is at hb
    rcases List.mem_cons.mp hb with heq | hb
    · exact heq ▸ hsep
    · exact forall_mem_join hdot is i (h i (by simp))
        (fun z hz => h z (List.mem_cons_of_mem _ hz)) b hb

/-! ## 健全性 -/

theorem assemble_sound {core : List Byte} {pre build : Option (List Byte)} {c : Components}
    (h : assemble core pre build = some c) :
    c.major ++ Ascii.dot :: (c.minor ++ Ascii.dot :: c.patch) = core ∧
      c.preRelease = parseIdentifiers pre ∧ c.build = parseIdentifiers build := by
  have hj := join_splitOn Ascii.dot core
  unfold assemble at h
  revert h hj
  generalize splitOn Ascii.dot core = r
  rcases r with ⟨major, _ | ⟨minor, _ | ⟨patch, _ | ⟨x, xs⟩⟩⟩⟩
  · intro h; simp at h
  · intro h; simp at h
  · intro h hj
    simp at h
    subst h
    exact ⟨hj, rfl, rfl⟩
  · intro h; simp at h

/-- 分解が成功したら、構成要素を文字列に戻すと入力と一致する。 -/
theorem decompose_sound {s : List Byte} {c : Components} (h : decompose s = some c) :
    c.render = s := by
  obtain ⟨hcore, hpre, hbuild⟩ := assemble_sound h
  unfold Components.render
  rw [hcore, hpre, hbuild, joinIdentifiers_parseIdentifiers, joinIdentifiers_parseIdentifiers,
    ← List.append_assoc, splitFirst_reassemble, splitFirst_reassemble]

theorem parse_eq_some_iff {s : List Byte} {c : Components} :
    parse s = some c ↔ decompose s = some c ∧ c.WF := by
  unfold parse
  cases hd : decompose s with
  | none => simp
  | some c' =>
    by_cases hwf : c'.WF
    · simp only [hwf, ite_true, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hwf⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [hwf, ite_false, Option.some.injEq]
      constructor
      · intro h; cases h
      · rintro ⟨rfl, h⟩; exact absurd h hwf

/-- `parse` が成功したら、結果は妥当で、文字列に戻すと入力と一致する。 -/
theorem parse_sound {s : List Byte} {c : Components} (h : parse s = some c) :
    c.WF ∧ c.render = s :=
  ⟨(parse_eq_some_iff.mp h).2, decompose_sound (parse_eq_some_iff.mp h).1⟩

/-! ## 完全性 -/

/-- 妥当な構成要素を文字列にして分解すると、元の構成要素が得られる。 -/
theorem decompose_complete {c : Components} (h : c.WF) : decompose c.render = some c := by
  rcases c with ⟨M, m, p, pre, build⟩
  obtain ⟨hM, hm, hp, hpre, hbuild⟩ := h
  have hdotM : Ascii.dot ∉ M := fun hmem => not_isDigit_dot (hM.forall_isDigit _ hmem)
  have hdotm : Ascii.dot ∉ m := fun hmem => not_isDigit_dot (hm.forall_isDigit _ hmem)
  have hdotp : Ascii.dot ∉ p := fun hmem => not_isDigit_dot (hp.forall_isDigit _ hmem)
  have hdotPre : ∀ i ∈ pre, Ascii.dot ∉ i := fun i hi hmem =>
    not_isIdentifierCharacter_dot ((hpre i hi).forall_isIdentifierCharacter _ hmem)
  have hdotBuild : ∀ i ∈ build, Ascii.dot ∉ i := fun i hi hmem =>
    not_isIdentifierCharacter_dot ((hbuild i hi).forall_isIdentifierCharacter _ hmem)
  -- コア部分のバイトは数字かドット
  have hcoreBytes : ∀ b ∈ M ++ Ascii.dot :: (m ++ Ascii.dot :: p), IsDigit b ∨ b = Ascii.dot :=
    forall_mem_join (q := fun b => IsDigit b ∨ b = Ascii.dot) (Or.inr rfl) [m, p] M
      (fun b hb => Or.inl (hM.forall_isDigit b hb))
      (fun y hy b hb => by
        simp at hy
        rcases hy with rfl | rfl
        · exact Or.inl (hm.forall_isDigit b hb)
        · exact Or.inl (hp.forall_isDigit b hb))
  -- プレリリース部分のバイトは識別子文字かドット
  have hpreBytes : ∀ b ∈ suffix Ascii.hyphen (joinIdentifiers pre),
      IsIdentifierCharacter b ∨ b = Ascii.dot :=
    forall_mem_suffix_joinIdentifiers (q := fun b => IsIdentifierCharacter b ∨ b = Ascii.dot)
      (Or.inl isIdentifierCharacter_hyphen) (Or.inr rfl)
      (fun i hi b hb => Or.inl ((hpre i hi).forall_isIdentifierCharacter b hb))
  have hplus : Ascii.plus ∉
      (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) ++ suffix Ascii.hyphen (joinIdentifiers pre) := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases hcoreBytes _ hmem with hd | hd
      · exact not_isDigit_plus hd
      · exact absurd hd (by decide)
    · rcases hpreBytes _ hmem with hd | hd
      · exact not_isIdentifierCharacter_plus hd
      · exact absurd hd (by decide)
  have hhyphen : Ascii.hyphen ∉ M ++ Ascii.dot :: (m ++ Ascii.dot :: p) := by
    intro hmem
    rcases hcoreBytes _ hmem with hd | hd
    · exact not_isDigit_hyphen hd
    · exact absurd hd (by decide)
  have hsplit : splitOn Ascii.dot (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) = (M, [m, p]) :=
    splitOn_join [m, p] M hdotM (fun y hy => by
      simp at hy
      rcases hy with rfl | rfl
      · exact hdotm
      · exact hdotp)
  have hrender : Components.render ⟨M, m, p, pre, build⟩ =
      ((M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) ++ suffix Ascii.hyphen (joinIdentifiers pre))
        ++ suffix Ascii.plus (joinIdentifiers build) := by
    simp [Components.render]
  unfold decompose
  simp only [hrender, splitFirst_append_suffix hplus, splitFirst_append_suffix hhyphen]
  unfold assemble
  rw [hsplit]
  simp [parseIdentifiers_joinIdentifiers hdotPre, parseIdentifiers_joinIdentifiers hdotBuild]

/-- 妥当な構成要素を文字列にして `parse` すると、元の構成要素が得られる。 -/
theorem parse_complete {c : Components} (h : c.WF) : parse c.render = some c :=
  parse_eq_some_iff.mpr ⟨decompose_complete h, h⟩

/-- 妥当な構成要素は、文字列が同じなら等しい(構文解析の結果は一意)。 -/
theorem Spec.Components.render_injective {c₁ c₂ : Components} (h₁ : c₁.WF) (h₂ : c₂.WF)
    (h : c₁.render = c₂.render) : c₁ = c₂ :=
  Option.some.inj ((parse_complete h₁).symm.trans (h ▸ parse_complete h₂))

/-- 妥当な構成要素が等しいことと、文字列にしたものが等しいことは同じ。 -/
theorem Spec.Components.eq_iff_render_eq {c₁ c₂ : Components} (h₁ : c₁.WF) (h₂ : c₂.WF) :
    c₁ = c₂ ↔ c₁.render = c₂.render :=
  ⟨fun h => h ▸ rfl, Components.render_injective h₁ h₂⟩

/-! ## BNF との対応 -/

theorem dotSeparatedPreReleaseIdentifiers_join : ∀ (is : List (List Byte)) (i : List Byte),
    (∀ x ∈ i :: is, PreReleaseIdentifier x) →
      DotSeparatedPreReleaseIdentifiers (join Ascii.dot i is)
  | [], i, h => .single (h i (by simp))
  | j :: js, i, h =>
    .cons (i := i) (rest := join Ascii.dot j js) (h i (by simp))
      (dotSeparatedPreReleaseIdentifiers_join js j
        (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem dotSeparatedPreReleaseIdentifiers_iff (s : List Byte) :
    DotSeparatedPreReleaseIdentifiers s ↔
      ∃ i is, (∀ x ∈ i :: is, PreReleaseIdentifier x) ∧ s = join Ascii.dot i is := by
  constructor
  · intro h
    induction h with
    | single hi => exact ⟨_, [], by simpa using hi, rfl⟩
    | cons hi _ ih =>
      obtain ⟨j, js, hall, rfl⟩ := ih
      refine ⟨_, j :: js, fun x hx => ?_, rfl⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hi
      · exact hall x hx
  · rintro ⟨i, is, hall, rfl⟩
    exact dotSeparatedPreReleaseIdentifiers_join is i hall

theorem dotSeparatedBuildIdentifiers_join : ∀ (is : List (List Byte)) (i : List Byte),
    (∀ x ∈ i :: is, BuildIdentifier x) → DotSeparatedBuildIdentifiers (join Ascii.dot i is)
  | [], i, h => .single (h i (by simp))
  | j :: js, i, h =>
    .cons (i := i) (rest := join Ascii.dot j js) (h i (by simp))
      (dotSeparatedBuildIdentifiers_join js j (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem dotSeparatedBuildIdentifiers_iff (s : List Byte) :
    DotSeparatedBuildIdentifiers s ↔
      ∃ i is, (∀ x ∈ i :: is, BuildIdentifier x) ∧ s = join Ascii.dot i is := by
  constructor
  · intro h
    induction h with
    | single hi => exact ⟨_, [], by simpa using hi, rfl⟩
    | cons hi _ ih =>
      obtain ⟨j, js, hall, rfl⟩ := ih
      refine ⟨_, j :: js, fun x hx => ?_, rfl⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hi
      · exact hall x hx
  · rintro ⟨i, is, hall, rfl⟩
    exact dotSeparatedBuildIdentifiers_join is i hall

/-- BNF で妥当な文字列とは、妥当な構成要素を文字列にしたものである。 -/
theorem validSemVer_iff_components (s : List Byte) :
    ValidSemVer s ↔ ∃ c : Components, c.WF ∧ c.render = s := by
  constructor
  · intro h
    cases h with
    | core hc =>
      cases hc with
      | mk hM hm hp =>
        exact ⟨⟨_, _, _, [], []⟩, ⟨hM, hm, hp, by simp, by simp⟩,
          by simp [Components.render, joinIdentifiers, suffix]⟩
    | corePreRelease hc hpre =>
      cases hc with
      | mk hM hm hp =>
        obtain ⟨i, is, hall, rfl⟩ := (dotSeparatedPreReleaseIdentifiers_iff _).mp hpre
        exact ⟨⟨_, _, _, i :: is, []⟩, ⟨hM, hm, hp, hall, by simp⟩,
          by simp [Components.render, joinIdentifiers, suffix]⟩
    | coreBuild hc hbuild =>
      cases hc with
      | mk hM hm hp =>
        obtain ⟨b, bs, hall, rfl⟩ := (dotSeparatedBuildIdentifiers_iff _).mp hbuild
        exact ⟨⟨_, _, _, [], b :: bs⟩, ⟨hM, hm, hp, by simp, hall⟩,
          by simp [Components.render, joinIdentifiers, suffix]⟩
    | corePreReleaseBuild hc hpre hbuild =>
      cases hc with
      | mk hM hm hp =>
        obtain ⟨i, is, hallPre, rfl⟩ := (dotSeparatedPreReleaseIdentifiers_iff _).mp hpre
        obtain ⟨b, bs, hallBuild, rfl⟩ := (dotSeparatedBuildIdentifiers_iff _).mp hbuild
        exact ⟨⟨_, _, _, i :: is, b :: bs⟩, ⟨hM, hm, hp, hallPre, hallBuild⟩,
          by simp [Components.render, joinIdentifiers, suffix]⟩
  · rintro ⟨⟨M, m, p, pre, build⟩, hwf, rfl⟩
    have hcore : VersionCore (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) :=
      .mk hwf.major hwf.minor hwf.patch
    cases pre with
    | nil =>
      cases build with
      | nil =>
        have hrender : Components.render ⟨M, m, p, [], []⟩ =
            M ++ Ascii.dot :: (m ++ Ascii.dot :: p) := by
          simp [Components.render, joinIdentifiers, suffix]
        rw [hrender]
        exact .core hcore
      | cons b bs =>
        have hrender : Components.render ⟨M, m, p, [], b :: bs⟩ =
            (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) ++ Ascii.plus :: join Ascii.dot b bs := by
          simp [Components.render, joinIdentifiers, suffix]
        rw [hrender]
        exact .coreBuild hcore (dotSeparatedBuildIdentifiers_join bs b hwf.build)
    | cons i is =>
      cases build with
      | nil =>
        have hrender : Components.render ⟨M, m, p, i :: is, []⟩ =
            (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) ++ Ascii.hyphen :: join Ascii.dot i is := by
          simp [Components.render, joinIdentifiers, suffix]
        rw [hrender]
        exact .corePreRelease hcore (dotSeparatedPreReleaseIdentifiers_join is i hwf.preRelease)
      | cons b bs =>
        have hrender : Components.render ⟨M, m, p, i :: is, b :: bs⟩ =
            (M ++ Ascii.dot :: (m ++ Ascii.dot :: p)) ++
              Ascii.hyphen :: (join Ascii.dot i is ++ Ascii.plus :: join Ascii.dot b bs) := by
          simp [Components.render, joinIdentifiers, suffix]
        rw [hrender]
        exact .corePreReleaseBuild hcore
          (dotSeparatedPreReleaseIdentifiers_join is i hwf.preRelease)
          (dotSeparatedBuildIdentifiers_join bs b hwf.build)

/-- BNF で妥当であることと、参照パーサが成功することは同値。 -/
theorem validSemVer_iff_parse (s : List Byte) : ValidSemVer s ↔ ∃ c, parse s = some c := by
  constructor
  · intro h
    obtain ⟨c, hwf, rfl⟩ := (validSemVer_iff_components s).mp h
    exact ⟨c, parse_complete hwf⟩
  · rintro ⟨c, h⟩
    exact (validSemVer_iff_components s).mpr ⟨c, parse_sound h⟩

/-- 文法上の妥当性は決定可能。 -/
instance (s : List Byte) : Decidable (ValidSemVer s) :=
  decidable_of_iff ((parse s).isSome = true)
    (by rw [validSemVer_iff_parse, Option.isSome_iff_exists])

end SemVer
