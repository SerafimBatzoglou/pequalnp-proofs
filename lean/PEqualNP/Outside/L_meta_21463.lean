import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21463 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8856 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or,[0,1]⟩,
      ⟨.or,[0,2]⟩,
      ⟨.and,[1,2]⟩,
      ⟨.or,[7,3]⟩,
      ⟨.and,[5,4]⟩,
      ⟨.and,[6,8]⟩,
      ⟨.or,[9,10]⟩],11⟩
  refine ⟨C,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
