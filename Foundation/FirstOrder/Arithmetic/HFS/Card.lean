module

Cardinality of hereditarily finite sets

def CardLE (a b : V) : Prop := ∃ f, domain f = a and range f = b and Injective f

def CardEQ (a b : V) : Prop := CardLE a b and CardLE b a

lemma card_exists_unique (a : V) : ∃! n, CardEQ (under n) a := by
  refine insert_induction ?_ ?_ ?_
  sorry
