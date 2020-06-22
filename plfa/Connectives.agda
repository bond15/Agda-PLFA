module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_ ; _⇔_ ; ≃-refl ; extensionality)
open plfa.Isomorphism.≃-Reasoning

data _x_ (A B : Set) : Set where
  ⟨_,_⟩ : -- introduction rule x-I
       A
    -> B
    -----
    -> A x B

π₁ : ∀ {A B : Set} -- elimination rule x-E₁
  -> A x B
  --------
  -> A
π₁ ⟨ a , b ⟩ = a

π₂ : ∀ {A B : Set} --- elimination rule x-E­₂
  -> A x B
  --------
  -> B
π₂ ⟨ a , b ⟩ = b


-- elimination after introduction result in initial term
η-x : ∀ {A B : Set} (w : A x B) -> ⟨ π₁ w , π₂ w ⟩ ≡ w
η-x ⟨ a , b ⟩ = refl

infixr 2 _x_

x-comm : ∀ {A B : Set} -> A x B ≃ B x A
x-comm = record
  { to  = λ { ⟨ a , b ⟩ -> ⟨ b , a ⟩ }
  ; from = λ { ⟨ b , a ⟩ -> ⟨ a , b ⟩}
  ; to∘from = λ { ⟨ b , a ⟩ -> refl }
  ; from∘to = λ { ⟨ a , b ⟩ -> refl }
  }

x-assoc : ∀ {A B C : Set} -> (A x B) x C ≃ A x (B x C)
x-assoc = record
  { to = λ { ⟨ ⟨ a , b ⟩ , c ⟩ -> ⟨ a , ⟨ b , c ⟩ ⟩}
  ; from = λ {⟨ a , ⟨ b , c ⟩ ⟩ -> ⟨ ⟨ a , b ⟩ , c ⟩}
  ; from∘to = λ { ⟨ ⟨ a , b ⟩ , c ⟩ -> refl }
  ; to∘from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ -> refl }
  }

-- basically an exercise of converting between internal product type
-- and record type
-- iff is isomorphic to product of functions
⇔≃x : ∀ {A B : Set} -> (A ⇔ B) ≃ ((A -> B) x (B -> A))
⇔≃x = record
  { to = λ { A⇔B -> ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩}
  ; from = λ { ⟨ to' , from' ⟩ -> record { to = to' ; from = from' } }
  ; from∘to = λ { A⇔B -> refl}
  ; to∘from = λ { ⟨ to' , from' ⟩ -> refl}
  }

-- aka Unit
data ⊤ : Set where -- no elim rule for ⊤
  tt :      -- introduction ⊤-I
    -------
    ⊤

-- any term of type ⊤ is tt
η-⊤ : ∀ (w : ⊤) -> tt ≡ w
η-⊤ tt = refl


-- 1 x c = c  algebraically/numerically
⊤-identityˡ : ∀ {A : Set} -> ⊤ x A ≃ A
⊤-identityˡ = record
  { to = λ { ⟨ tt , a ⟩ -> a}
  ; from = λ{ a -> ⟨ tt , a ⟩}
  ; from∘to = λ { ⟨ tt , a ⟩ -> refl }
  ; to∘from = λ { a -> refl}
  }

-- simple example reasoning with equality
⊤-identityʳ : ∀ {A : Set} -> A x ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A x ⊤)
  ≃⟨ x-comm ⟩
    (⊤ x A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- \U+
-- coproduct
data _⨄_ (A B : Set) : Set where
  inj₁ : -- introduction rule  ⊎-I₁
    A
    ----
    -> A ⨄ B

  inj₂ : -- ⊎-I₁
    B
    ---
    -> A ⨄ B


case-⨄ : ∀ {A B C : Set} -- elimination rule ⊎-E
  -> (A -> C)
  -> (B -> C)
  -> A ⨄ B
  -----------
  -> C
case-⨄ f g (inj₁ a) = f a
case-⨄ f g (inj₂ b) = g b

η-⨄ : ∀ {A B : Set} (w : A ⨄ B) -> case-⨄ inj₁ inj₂ w ≡ w
η-⨄ (inj₁ a) = refl
η-⨄ (inj₂ b) = refl

infixr 1 _⨄_

⨄-comm : ∀ {A B : Set} -> A ⨄ B ≃ B ⨄ A
⨄-comm = record
  { to = λ x -> case-⨄ inj₂ inj₁ x
  ; from = λ x -> case-⨄ inj₂ inj₁ x
  ; from∘to = λ { (inj₁ _ ) -> refl ; (inj₂ _) -> refl}
  ; to∘from = λ { (inj₁ _ ) -> refl ; (inj₂ _) -> refl}
  }


data ⊥ : Set where
-- no introduction rules

⊥-elim : ∀ {A : Set} -- ⊥-E  absurd
  -> ⊥
  -----
  -> A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ -> C)(w : ⊥) -> ⊥-elim w ≡ h w
uniq-⊥ h ()

identity : ∀ {A : Set} (a : A) -> A
identity a = a


-- 0 + A = A
⊥-identityˡ : ∀ {A B C : Set} -> ⊥ ⨄ A ≃ A
⊥-identityˡ = record
  { to = λ x -> case-⨄ ⊥-elim identity x
  ; from = λ a -> inj₂ a
  -- x : ⊥ ⨄ A
  ; from∘to = λ { (inj₁ u) -> ⊥-elim u ;
                  (inj₂ a) -> refl }
  ; to∘from = λ a -> refl
  }

⊥-identityʳ : ∀ {A B C : Set} -> A ⨄ ⊥ ≃ A
⊥-identityʳ {A} {B} {C} =
  ≃-begin
    (A ⨄ ⊥)
  ≃⟨ ⨄-comm ⟩
    (⊥ ⨄ A)
  ≃⟨ ⊥-identityˡ {A} {B} {C}⟩
      A
  ≃-∎


-- Implication

-- λ  →-I
-- →-E
→-elim : ∀ {A B : Set}
  -> (A -> B)
  -> A
  -----------
  -> B

→-elim f a = f a

η-→ : ∀ {A B : Set} (f : A -> B) -> (λ (x : A) -> f x) ≡ f
η-→ f = refl

-- p ^ n ^ m = p ^ (n * m)
currying : ∀ {A B C : Set} -> (A -> B -> C) ≃ (A x B -> C)
currying = record
  { to = λ f -> λ axb -> (f (π₁ axb) (π₂ axb))
  ; from = λ f -> λ a -> λ b -> f ⟨ a , b ⟩
  ; from∘to = λ a -> refl
  ; to∘from = λ f -> extensionality λ {⟨ a , b ⟩ -> refl }
  }
-- extensionality is still a postulate without cubical Agda









--
