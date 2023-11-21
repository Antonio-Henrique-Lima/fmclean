
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,intro hp,exact hp p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,by_cases p:P,exact p,exfalso,exact hp p,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,intro hp,by_cases p:P,exact p,exfalso,exact hp p,intro p,intro hp,exact hp p,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,cases pq,right,exact pq,left,exact pq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,split,cases pq,exact pq_right,cases pq,exact pq_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hp,intro p,cases hp,exfalso,exact hp p,exact hp,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hp,intro np,cases hp,exfalso,exact np hp,exact hp,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hp,intro nq,intro p,have q : Q := hp p,apply nq,exact q,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hp,intro p,by_cases q:Q,exact q,have hq := hp q,exfalso,exact hq p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,intro hp,intro nq,intro p,have q : Q := hp p,exact nq q,intro hq,intro p,by_cases q:Q,exact q,have hp := hq q,exfalso,exact hp p,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hp,apply hp,right,intro p,apply hp,left,exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hp,intro np,apply np,apply hp,intro p,exfalso,exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,intro hp,cases hp,cases pq,exact hp_left pq,exact hp_right pq,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,intro hp,cases pq,cases hp,exact hp pq_left,exact hp pq_right,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro hp,split,intro p,apply hp,left,exact p,intro q,apply hp,right,exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hp,intro h,cases hp,cases h,exact hp_left h,exact hp_right h,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hp,by_cases p:P,left,intro q,apply hp,split,exact p,exact q,right,exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hp,intro h,cases h,cases hp,exact hp h_right,exact hp h_left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,exact demorgan_conj P Q,exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,exact demorgan_disj P Q,exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hp,cases hp,cases hp_right,left,split,exact hp_left,exact hp_right,right,split,exact hp_left,exact hp_right,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hp,cases hp,cases hp,split,exact hp_left,left,exact hp_right,cases hp,split,exact hp_left,right,exact hp_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hp,split,cases hp,left,exact hp,cases hp,right,exact hp_left,cases hp,left,exact hp,cases hp,right,exact hp_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hp,cases hp,cases hp_left,left,exact hp_left,cases hp_right,left,exact hp_right,right,split,exact hp_left,exact hp_right,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro hp,intro p,intro q,apply hp,split,exact p,exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hp,intro pq,cases pq,have hj := hp pq_left,have r : R := hj pq_right,exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,left,exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,right,exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,cases pq,exact pq_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,cases pq,exact pq_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,intro pp,cases pp,exact pp_left,intro p,split,exact p,exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,intro pp,cases pp,exact pp,exact pp,intro p,left,exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hp,intro x,intro np,apply hp,existsi x,exact np,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hp,intro h,cases h with x hx,have p:= hp x,apply p,exact hx,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hp,by_contra h,apply hp,intro x,by_contra hc,apply h,existsi x,exact hc,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hp,intro hc,cases hp with a ha,apply ha,have hpa := hc a,exact hpa,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,exact demorgan_forall U P,exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,exact demorgan_exists U P,exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hp,intro hc,cases hp with x hx,have nhx := hc x,exact nhx hx,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hp,intro hc,cases hc with x hx,apply hx,have px := hp x,exact px,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hp,intro x,by_contra hc,apply hp,existsi x,exact hc,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro hp,by_contra hc,apply hp,intro x,intro px,apply hc,existsi x,exact px,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,exact forall_as_neg_exists U P,exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,exact exists_as_neg_forall U P,exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro hp,cases hp with x hx,split,existsi x,cases hx,exact hx_left,existsi x,cases hx,exact hx_right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro hp,cases hp with x hx,cases hx,left,existsi x,exact hx,right,existsi x,exact hx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro hp,cases hp,cases hp with x hx,existsi x,left,exact hx,cases hp with x hx,existsi x,right,exact hx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hp,split,intro x,have px := hp x,cases px,exact px_left,intro x,have qx := hp x,cases qx,exact qx_right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hp,cases hp,intro x,split,have px := hp_left x,exact px,have qx := hp_right x,exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hp,intro x,cases hp,left,have px := hp x,exact px,right,have qx := hp x,exact qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
