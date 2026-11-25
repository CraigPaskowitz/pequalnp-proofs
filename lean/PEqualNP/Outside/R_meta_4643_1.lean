import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4643_1
    (normalize :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 13 → C.output = 22 →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 13 ∧ D.output = 22 ∧
          (∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[t]? = some g →
            ∀ i ∈ g.inputs, i < 10 + t ∨ i = 23) ∧
          (∀ t j : ℕ, j < 10 →
            (∀ g ∈ C.gates.take t, j ∉ g.inputs) →
            ∀ g ∈ D.gates.take t, j ∉ g.inputs) ∧
          ((∃ g ∈ C.gates, 9 ∈ g.inputs) → ∃ g ∈ D.gates, 9 ∈ g.inputs) ∧
          (∀ xs : List Bool, xs.length = 10 → D.wires xs = C.wires xs))
    (bounded :
      let F := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      let W := fun (C : PEqualNP.CircuitLowerBounds.Circuit) k x =>
        (C.wires (X x)).getD k false
      ∀ (j : Fin 9) (D : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ) (b : Bool),
        j ≠ 0 → j ≠ 6 → PEqualNP.MetaComplexity.FanInTwo D →
        D.size = 13 → D.output = 22 → 10 ≤ k → k < 22 →
        (∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[t]? = some g →
          ∀ i ∈ g.inputs, i < 10 + t ∨ i = 23) →
        (b = false → k = 10 → j = 1 ∨ j = 4 ∨ j = 7) →
        (∀ g ∈ D.gates.take (k+1-10), j.val ∉ g.inputs) →
        (∀ x, F x ≠ F (Function.update x j (!(x j))) → W D k x = !b) →
        (∃ g ∈ D.gates, 9 ∈ g.inputs) →
        (∃ x, x j = !b ∧ W D k x = b ∧ D.eval (X x) ≠ F x) →
        ∃ x, D.eval ((X x).set j.val (if b then x j || W D k x else x j && W D k x)) ≠ F x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (9 : ℕ) → Bool) => (x3.wires (x2 x5)).getD x4 Bool.false; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool), x4 ≠ (0 : Fin (9 : ℕ)) → x4 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size = (13 : ℕ) → x5.output = (22 : ℕ) → (10 : ℕ) ≤ x6 → x6 < (22 : ℕ) → (x7 = Bool.false → x6 = (10 : ℕ) → x4 = (1 : Fin (9 : ℕ)) ∨ x4 = (4 : Fin (9 : ℕ)) ∨ x4 = (7 : Fin (9 : ℕ))) → (∀ x16 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x16.inputs) → (∀ (x17 x18 : Fin (9 : ℕ) → Bool), (∀ (x19 : Fin (9 : ℕ)), x19 ≠ x4 → x17 x19 = x18 x19) → x1 x17 ≠ x1 x18 → x3 x5 x6 x17 = !x7) → (∃ x18 ∈ x5.gates, (9 : ℕ) ∈ x18.inputs) → (∃ (x19 : Fin (9 : ℕ) → Bool), x19 x4 = !x7 ∧ x3 x5 x6 x19 = x7 ∧ x5.eval (x2 x19) ≠ x1 x19) → ∃ (x20 : Fin (9 : ℕ) → Bool), x5.eval ((x2 x20).set (↑x4) (if x7 = Bool.true then x20 x4 || x3 x5 x6 x20 else x20 x4 && x3 x5 x6 x20)) ≠ x1 x20 := by
  dsimp only at bounded ⊢
  intro j C k b hj0 hj6 hfan hsize hout hlo hhi hearly hpre hdom hseed hbad
  obtain ⟨D, dfan, dsize, dout, dreads, dpre, dseed, deq⟩ :=
    normalize C hfan hsize hout
  let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  have same (x : Fin 9 → Bool) :
      D.wires (List.ofFn x ++ [x 0 || x 6]) = C.wires (List.ofFn x ++ [x 0 || x 6]) :=
    deq _ (by simp [X])
  have sameEval (xs : List Bool) (len : xs.length = 10) : D.eval xs = C.eval xs := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [deq xs len, dout, hout]
  obtain ⟨x, bad⟩ := bounded j D k b hj0 hj6 dfan dsize dout hlo hhi dreads hearly
    (dpre _ _ (by have := j.isLt; omega) hpre)
    (fun x h => by
      rw [same]
      exact hdom x (Function.update x j (!(x j)))
        (fun i hi => (Function.update_of_ne hi _ _).symm) h)
    (dseed hseed)
    (by
      obtain ⟨x, hx, hw, he⟩ := hbad
      refine ⟨x, hx, ?_, ?_⟩
      · rw [same]; exact hw
      · rw [sameEval (List.ofFn x ++ [x 0 || x 6]) (by simp)]; exact he)
  refine ⟨x, ?_⟩
  rw [same] at bad
  rw [sameEval ((List.ofFn x ++ [x 0 || x 6]).set j.val
    (if b then x j || (C.wires (X x)).getD k false
      else x j && (C.wires (X x)).getD k false)) (by simp)] at bad
  exact bad
