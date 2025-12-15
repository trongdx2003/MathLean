import Mathlib.Tactic

lemma aux_list_exists_last_elem (l : List Nat) (h : l.length ≥ 1) :
  ∃ x l', l = l' ++ [x] := by
  induction' l with a l
  · norm_num at h
  · rename_i h_tail
    induction l_length : l.length with
    | zero => use a, []; simp at *; exact l_length
    | succ m => obtain ⟨k, ⟨L, hL⟩⟩ := h_tail (by linarith)
                use k, a :: L
                rw [hL]
                rfl


@[simp] def isSorted : List ℕ → Prop
  | [] => True
  | _ :: [] => True
  | x :: y :: xs => if x > y then False else (isSorted (y :: xs))


theorem aux_list_sorted_by_add_one_iff (x : ℕ) (l : List ℕ) (h : l.length ≥ 1) (sortedl : isSorted l) :
  x ≥ l.getLast! ↔ isSorted (l ++ [x]) := by
    induction l_length : l.length generalizing l with
    | zero => linarith
    | succ m => rename_i hl
                cases l
                · norm_num at l_length
                · simp at l_length
                  rename_i head tail
                  cases tail
                  · simp
                  · simp at sortedl hl
                    simp
                    rename_i head' tail
                    have : (head' :: tail).getLast?.getD 0 ≤ x ↔ isSorted (head' :: tail ++ [x]) := by
                      apply hl
                      · simp
                      · exact sortedl.right
                      · exact l_length
                    tauto


theorem aux_list_sorted_right_cancel_one_elem (l : List ℕ) (x : ℕ) : isSorted (l ++ [x]) → isSorted l := by
  intro h
  induction l_length : l.length generalizing l with
  | zero => simp at l_length; rw [l_length]; trivial
  | succ m => rename_i hl
              cases l
              · norm_num at l_length
              · rename_i _ tail
                simp at l_length
                cases tail
                · trivial
                · simp
                  simp at h
                  exact ⟨h.left, hl _ h.right l_length⟩


theorem aux_list_sorted_left_cancel (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted bs := by
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length; rw [as_length] at h; simpa [h]
  | succ m => rename_i hl
              obtain ⟨x, c, hxc⟩ := aux_list_exists_last_elem as (by linarith)
              rw [hxc] at as_length h
              simp at as_length
              rw [List.append_assoc] at h
              have sorted_x_bs : isSorted ([x] ++ bs) := hl c ([x] ++ bs) h as_length
              cases bs
              · trivial
              · simp at sorted_x_bs
                exact sorted_x_bs.right


theorem aux_list_sorted_right_cancel (as bs : List ℕ) (h : isSorted (as ++ bs)) : isSorted as := by
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length; rw [as_length]; trivial
  | succ m => rename_i hl
              cases as
              · trivial
              · simp at as_length
                rename_i _ tail
                cases tail
                · trivial
                · simp at h
                  simp
                  exact ⟨h.left, hl _ _ h.right as_length⟩


@[simp] def isEqual : List ℕ → List ℕ → Prop
  | [], [] => True
  | [], _ => False
  | _, [] => False
  | x :: xs, y :: ys => if x != y then False else isEqual xs ys


theorem aux_list_eq_imp_eq_by_add_one_elem (as bs : List ℕ) (h : isEqual as bs) : ∀ x, isEqual (as ++ [x]) (bs ++ [x]) := by
  intro x
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length
            simp [as_length] at *
            cases bs
            · simp
            · simp at h
  | succ m => rename_i hl
              cases as
              · norm_num at as_length
              · simp at as_length
                cases bs
                · simp at h
                · simp at h
                  simp
                  exact ⟨h.left, hl _ _ h.right as_length⟩


theorem aux_list_eq_imp_eq_by_add_a_list (as bs : List ℕ) (h : isEqual as bs) : ∀ (cs : List ℕ), isEqual (as ++ cs) (bs ++ cs) := by
  intro cs
  induction cs_length : cs.length generalizing cs with
  | zero => simp at cs_length
            rw [cs_length]
            simp [h]
  | succ m => rename_i hl
              obtain ⟨x, cs', h_x_cs⟩ := aux_list_exists_last_elem cs (by linarith)
              rw [h_x_cs] at cs_length
              rw [h_x_cs, ← List.append_assoc, ← List.append_assoc]
              apply aux_list_eq_imp_eq_by_add_one_elem
              simp at cs_length
              exact hl cs' cs_length


theorem aux_list_add_one_eq_imp_list_eq (as bs : List ℕ) (x : ℕ) : isEqual (as ++ [x]) (bs ++ [x]) → isEqual as bs := by
  intro h
  induction as_length : as.length generalizing as bs with
  | zero => simp at as_length
            rw [as_length]
            cases bs
            · simp
            · simp [as_length] at h
  | succ m => rename_i hl
              cases as
              · norm_num at as_length
              · simp at as_length
                cases bs
                · simp at h
                · simp at h
                  simp
                  exact ⟨h.left, hl _ _ h.right as_length⟩


theorem aux_list_add_list_eq_imp_list_eq (as bs cs : List ℕ) : isEqual (as ++ cs) (bs ++ cs) → isEqual as bs := by
  intro h
  induction cs_length : cs.length generalizing cs with
  | zero => simp at cs_length
            rw [cs_length] at h
            simp at h
            exact h
  | succ m => rename_i hl
              obtain ⟨x, cs', h_x_cs⟩ := aux_list_exists_last_elem cs (by linarith)
              rw [h_x_cs] at cs_length h
              rw [← List.append_assoc, ← List.append_assoc] at h
              apply aux_list_add_one_eq_imp_list_eq at h
              simp at cs_length
              exact hl cs' h cs_length
