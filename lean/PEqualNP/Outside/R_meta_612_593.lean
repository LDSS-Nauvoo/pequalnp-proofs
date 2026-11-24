import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_593
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      PEqualNP.BicliqueBlockCost.HasBlockCost G C.size)
    (count : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (F : Finset (PEqualNP.BicliqueBlockCost.Block n)),
      PEqualNP.BicliqueBlockCost.IsBlockCover G F →
      (∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) →
      G.edgeSet.ncard ≤ F.sum PEqualNP.BicliqueBlockCost.blockCost) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hEdge hC4 hCover hMin hMono hEval
  let P : ℕ → Prop := fun s => ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    D.size = s ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C
  have hex : ∃ s, P s := ⟨C.size, C, rfl, hMono, rfl⟩
  obtain ⟨D, hSize, hMonoD, hEq⟩ := Nat.find_spec hex
  have hLe : D.size ≤ C.size := by
    rw [hSize]
    exact Nat.find_min' hex ⟨C, rfl, hMono, rfl⟩
  have hLeast : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D := by
    refine ⟨hMonoD, ?_⟩
    intro E hMonoE hEqE
    rw [hSize]
    exact Nat.find_min' hex ⟨E, rfl, hMonoE, hEqE.trans hEq⟩
  have hEvalD : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    have hx : D.eval (List.ofFn x) = C.eval (List.ofFn x) := congrFun hEq x
    rw [hx]
    exact hEval x
  obtain ⟨F, hF, hCost⟩ := normalize n G D hEdge hC4 hLeast hEvalD
  have hStar : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
    intro p hp
    by_contra! h
    obtain ⟨a, c, ha, hc, hac⟩ := Finset.one_lt_card_iff.mp h.1
    obtain ⟨b, d, hb, hd, hbd⟩ := Finset.one_lt_card_iff.mp h.2
    obtain ⟨hDisjoint, _, _, hAdj⟩ := hF.1 p hp
    have sep : ∀ u ∈ p.1, ∀ v ∈ p.2, u ≠ v := by
      rintro u hu v hv rfl
      exact Finset.disjoint_left.mp hDisjoint hu hv
    exact hC4 a b c d (sep _ ha _ hb) hac (sep _ ha _ hd) (sep _ hc _ hb).symm
      hbd (sep _ hc _ hd) (hAdj _ ha _ hb) (hAdj _ hc _ hb).symm
      (hAdj _ hc _ hd) (hAdj _ ha _ hd).symm
  have hCenters : ∃ S : Finset (Fin n),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card ≤ F.card := by
    have hCenter : ∀ p ∈ F, ∃ v : Fin n,
        ∀ u w, PEqualNP.BicliqueBlockCost.BlockCovers p u w → u = v ∨ w = v := by
      intro p hp
      obtain ⟨_, hA, hB, _⟩ := hF.1 p hp
      rcases hStar p hp with ha | hb
      · obtain ⟨v, hv⟩ := hA
        refine ⟨v, ?_⟩
        intro u w h
        rcases h with h | h
        · exact Or.inl ((Finset.card_le_one.mp ha) _ h.1 _ hv)
        · exact Or.inr ((Finset.card_le_one.mp ha) _ h.1 _ hv)
      · obtain ⟨v, hv⟩ := hB
        refine ⟨v, ?_⟩
        intro u w h
        rcases h with h | h
        · exact Or.inr ((Finset.card_le_one.mp hb) _ h.2 _ hv)
        · exact Or.inl ((Finset.card_le_one.mp hb) _ h.2 _ hv)
    let center : {p // p ∈ F} → Fin n := fun p => Classical.choose (hCenter p.1 p.2)
    let S : Finset (Fin n) := F.attach.image center
    refine ⟨S, ?_, ?_⟩
    · intro u v huv
      obtain ⟨p, hp, hCover⟩ := hF.2 u v huv
      have hc := Classical.choose_spec (hCenter p hp) u v hCover
      change u = center ⟨p, hp⟩ ∨ v = center ⟨p, hp⟩ at hc
      have hm : center ⟨p, hp⟩ ∈ S :=
        Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
      rcases hc with hu | hv
      · left
        rw [hu]
        exact hm
      · right
        rw [hv]
        exact hm
    · calc
        S.card ≤ F.attach.card := Finset.card_image_le
        _ = F.card := Finset.card_attach
  obtain ⟨S, hS, hCardS⟩ := hCenters
  have hBudget := count n G F hF hStar
  have ht : t ≤ S.card := hMin S hS
  have hPositive : 0 < F.card := by
    obtain ⟨u, v, huv⟩ := hEdge
    obtain ⟨p, hp, _⟩ := hF.2 u v huv
    exact Finset.card_pos.mpr ⟨p, hp⟩
  change F.sum PEqualNP.BicliqueBlockCost.blockCost + (F.card - 1) ≤ D.size at hCost
  omega
