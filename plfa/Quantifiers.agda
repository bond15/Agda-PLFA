module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import plfa.Isomorphism using (_≃_; extensionality)


-- ∀-I
-- λ (n : A) -> B x

∀-elim : ∀ {A : Set} {B : A -> Set}
  -> (L : ∀ (x : A) -> B x)
  -> (M : A)
  ---------------------------
  -> B M
∀-elim L M = L M

-- compare to →
--→-elim : ∀ {A B : Set}
--  -> (A -> B)
--  -> A
--  -----------
--  -> B


-- (B * C)ᴬ ≃ Bᴬ * Cᴬ
∀-distrib-x : ∀ {A : Set} {B C : A -> Set} ->
  (∀ (x : A) -> B x × C x) ≃ (∀ (x : A) -> B x) × (∀ (x : A) -> C x)
∀-distrib-x = record
  { to = λ{ f -> ⟨ (λ a -> (proj₁ (f a))) , (λ a -> (proj₂ (f a))) ⟩ }
  ; from = λ f×g -> λ a -> ⟨ (proj₁ f×g) a , (proj₂ f×g) a ⟩
  ; from∘to = λ a -> refl
  ; to∘from = λ f×g -> refl
  }


data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  _ : ∀ {B : Tri -> Set} ->  ∀ (x : Tri) -> B x ≃ (B aa × B bb × B cc)



-- Existentials

data Σ (A : Set) (B : A -> Set) : Set where
  ⟨_,_⟩ : (x : A) -> B x -> Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x -> B) = Σ[ x ∈ A ] B


-- syntax for when domain is left implicit
∃ : ∀ {A : Set} (B : A -> Set) -> Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x -> B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A -> Set} {C : Set}
  -> (∀ x -> B x -> C)
  -> ∃[ x ] B x
  ----------------------
  -> C
∃-elim f ⟨ x , bx ⟩ = f x bx





  --
