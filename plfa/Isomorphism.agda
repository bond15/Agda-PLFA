module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- lambda expression
id = λ (x : ℕ) -> x

_ : id 7 ≡ 7
_ = refl


data Bool : Set  where
  tt : Bool
  ff : Bool


-- lambda with case statements
not : Bool -> Bool
not = λ { tt -> ff ; ff -> tt}

_ : not tt ≡ ff
_ = refl

_ : Bool
_ = ( λ (x : Bool) -> x ) tt

-- similar to axiom in Coq
postulate
  -- extensionality for regular function types
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g
-- or you could prove this in Cubical Agda

-- Records
record foobar (A B : Set) : Set where
  field
    foo : A
    bar : B

fb : foobar Bool ℕ
fb = record { foo = tt ; bar = 7}

_ : Bool
_ = foobar.foo fb  -- haskell like record projectors
-- Isomorphism
-- \~-
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
    from∘to : ∀ (a : A) -> from (to a) ≡ a
    to∘from : ∀ (b : B) -> to (from b) ≡ b
open _≃_


-- ^^ This record syntax is equivalent to
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B
-- with component obtained by projection out of `mk-≃`
-- ex)
-- to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
-- to′ (mk-≃′ f g g∘f f∘g) = f




-- Properties of Isomorphism

-- Isomorphism is an equivalence
-- Isomorphism is Reflexive
≃-refl : ∀ {A : Set}
  ---------
  -> A ≃ A
≃-refl = record
  { to = λ{x -> x}
  ; from = λ{x -> x}
  ; from∘to = λ{a -> refl}
  ; to∘from = λ{b -> refl}
  }

-- Isomorphism is Symmetric
≃-sym : ∀ {A B : Set}
  -> A ≃ B
  --------
  -> B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }


open import Level
_∘_ : ∀ { ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} ->
  (B -> C) -> (A -> B) -> A -> C
(g ∘ f) a = g (f a)

≃-trans : ∀ {A B C : Set}
  -> A ≃ B
  -> B ≃ C
  --------
  -> A ≃ C
≃-trans A≃B B≃C = record
  { to = (to B≃C) ∘ (to A≃B)
  ; from = (from A≃B) ∘ (from B≃C)
  ; from∘to = λ{ a ->
      begin
        (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) a)
      ≡⟨⟩ -- unfold ∘ def
        (from A≃B (from B≃C (to B≃C (to A≃B a)))) -- A->B->C->B->A ≡ a
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B a)) ⟩
        -- (B->A) (A->B->C->B->A) ­≡ (B->A) a
        -- (B->A) (A -> B) a ≡ a ???
        (from∘to A≃B) a
      }
  ; to∘from = λ { c ->
      begin
        (to B≃C (to A≃B (from A≃B (from B≃C c))))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C c))⟩
        (to∘from B≃C) c
    }
  }


-- Equational reasoning with isomorphism
module ≃-Reasoning where
  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    -> A ≃ B
    --------
    -> A ≃ B

  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    -> A ≃ B
    -> B ≃ C
    --------
    -> A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
    --------
    -> A ≃ A
  A ≃-∎ = ≃-refl
open ≃-Reasoning


-- Another relation between types
-- Embedding
-- A weakening of isomorphism
-- an embedding shwos that the first type is included within the second
-- a many-to-one correspondence

-- \<~
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
    from∘to : ∀ (x : A) -> from (to x) ≡ x
    -- A->B->A is in A
open _≲_

-- Embegginds are reflexive, transitive, and anti-symmetric
-- Can also do equational reazoning with embeddings



-- equivalence of propositions - iff
-- \iff
record _⇔_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
-- show that this is an equivalence

⇔-refl : ∀ (A : Set)
  -----
  -> A ⇔ A
⇔-refl A = record
  { to = λ{a -> a}
  ; from = λ{a -> a}
  }

⇔-sym : ∀ {A B : Set}
  -> A ⇔ B
  --------
  -> B ⇔ A
⇔-sym A⇔B = record
  { to = _⇔_.from A⇔B
  ; from = _⇔_.to A⇔B
  }

⇔-trans : ∀ {A B C : Set}
  -> A ⇔ B
  -> B ⇔ C
  --------
  -> A ⇔ C

⇔-trans A⇔B B⇔C = record
  { to = (_⇔_.to B⇔C)∘(_⇔_.to A⇔B)
  ; from = (_⇔_.from A⇔B)∘(_⇔_.from B⇔C)
  }

data Unit : Set where
  unit : Unit


contr : ∀ (a : Unit) -> a ≡ unit
contr = λ { unit -> refl }

data isUnit : Unit -> Unit -> Set where
  isunit : isUnit unit unit

record Equiv-relation (A : Set) (R : A -> A -> Set) : Set₃ where
  field
    r-refl : ∀ (a : A) -> R a a
    r-sym : ∀ (a a' : A) -> R a a' -> R a' a
    r-trans : ∀ (a a' a'' : A) -> R a a' -> R a' a'' -> R a a''

_ : Equiv-relation Unit isUnit
_ = record
  { r-refl = λ { unit -> isunit }
  ; r-sym = λ { unit unit _ -> isunit }
  ; r-trans = λ { unit unit unit _ _ -> isunit }
  }
