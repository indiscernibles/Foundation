module

public import Foundation.FirstOrder.Arithmetic.HFS.Basic

@[expose] public section
/-!

# Cardinality of hereditarily finite sets

-/

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CardLE (a b : V) : Prop := ∃ f, domain f = a ∧ range f = b ∧ IsMapping.Injective f

#check IsMapping.injectiveDef

def CardLE.dfn : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “a b. ∃ f, !domainDef a f ∧ !rangeDef b f ∧ !IsMapping.InjectiveDef f”

infix:50 " ≤# " => CardLE

lemma CardLE.defined : 𝚺ᴬ₁-Relation[V] CardLE via CardLE.dfn := sorry

lemma CardLE.definable : 𝚺ᴬ₁-Relation[V] CardLE := CardLE.defined.to_definable

def CardEQ (a b : V) : Prop := CardLE a b ∧ CardLE b a

infix:60 " ≋ " => CardEQ

lemma CardEQ.defined : 𝚺ᴬ₁-Relation[V] CardEQ via CardEQ.dfn := sorry

lemma CardEQ.definable : 𝚺ᴬ₁-Relation[V] CardEQ := CardEQ.defined.to_definable

end FFL.FirstOrder.Arithmetic
