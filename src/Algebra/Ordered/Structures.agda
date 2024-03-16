------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordered algebraic structures (not packed up with sets, orders,
-- operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Algebra.Ordered`.

{-# OPTIONS --postfix-projections --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_)

module Algebra.Ordered.Structures
  {a ℓ₁ ℓ₂} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ₁)       -- The underlying equality relation
  (_≲_ : Rel A ℓ₂)       -- The underlying order relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Ordered.Definitions _≲_
open import Algebra.Structures _≈_
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (flip)
open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Definitions using (Transitive; Monotonic₁; Monotonic₂; AntitonicMonotonic)
open import Relation.Binary.Structures using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Consequences using (mono₂⇒cong₂)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

------------------------------------------------------------------------
-- Preordered structures

-- Preordered magmas (promagmas)

record IsPromagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder  : IsPreorder _≈_ _≲_
    ∙-cong      : Congruent₂ ∙
    mono        : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPreorder isPreorder public

  mono₁ : ∀ {x} → Monotonic₁ _≲_ _≲_ (flip ∙ x)
  mono₁ y≈z = mono y≈z refl

  mono₂ : ∀ {x} → Monotonic₁ _≲_ _≲_ (∙ x)
  mono₂ y≈z = mono refl y≈z

  isMagma : IsMagma ∙
  isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

  open IsMagma isMagma public using (setoid; ∙-congˡ; ∙-congʳ)

-- Preordered semigroups (prosemigroups)

record IsProsemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromagma  : IsPromagma ∙
    assoc       : Associative ∙

  open IsPromagma isPromagma public

  isSemigroup : IsSemigroup ∙
  isSemigroup = record { isMagma = isMagma ; assoc = assoc }

-- Preordered monoids (promonoids)

record IsPromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ∙
    identity       : Identity ε ∙

  open IsProsemigroup isProsemigroup public

  isMonoid : IsMonoid ∙ ε
  isMonoid = record { isSemigroup = isSemigroup ; identity = identity }

  open IsMonoid isMonoid public using (identityˡ; identityʳ)

-- Preordered commutative monoids (commutative promonoids)

record IsCommutativePromonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    comm        : Commutative ∙

  open IsPromonoid isPromonoid public

  isCommutativeMonoid : IsCommutativeMonoid ∙ ε
  isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeSemigroup)

-- Preordered semirings (prosemirings)

record IsProsemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePromonoid : IsCommutativePromonoid + 0#
    *-cong                   : Congruent₂ *
    *-mono                   : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                  : Associative *
    *-identity               : Identity 1# *
    distrib                  : * DistributesOver +
    zero                     : Zero 0# *

  open IsCommutativePromonoid +-isCommutativePromonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; mono₁                  to +-mono₁
    ; mono₂                  to +-mono₂
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    )

  *-isPromonoid : IsPromonoid * 1#
  *-isPromonoid = record
    { isProsemigroup = record
      { isPromagma   = record
        { isPreorder = isPreorder
        ; ∙-cong     = *-cong
        ; mono       = *-mono
        }
      ; assoc        = *-assoc
      }
    ; identity       = *-identity
    }

  open IsPromonoid *-isPromonoid public
    using ()
    renaming
    ( ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; mono₁       to *-mono₁
    ; mono₂       to *-mono₂
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    ; isMonoid    to *-isMonoid
    )

  isSemiring : IsSemiring + * 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid           = +-isCommutativeMonoid
      ; *-cong                          = *-cong
      ; *-assoc                         = *-assoc
      ; *-identity                      = *-identity
      ; distrib                         = distrib
      }
    ; zero                              = zero
    }

  open IsSemiring isSemiring public using (distribˡ; distribʳ; zeroˡ; zeroʳ)

------------------------------------------------------------------------
-- Partially ordered structures

-- Partially ordered magmas (pomagmas)

record IsPomagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≲_
    mono           : Monotonic₂ _≲_ _≲_ _≲_ ∙

  open IsPartialOrder isPartialOrder public

  ∙-cong : Congruent₂ ∙
  ∙-cong = mono₂⇒cong₂ _≈_ _≈_ Eq.sym reflexive antisym mono

  isPromagma : IsPromagma ∙
  isPromagma = record
    { isPreorder = isPreorder
    ; ∙-cong     = ∙-cong
    ; mono       = mono
    }

  open IsPromagma isPromagma public
    using (setoid; ∙-congˡ; ∙-congʳ; mono₁; mono₂; isMagma)

-- Partially ordered semigroups (posemigroups)

record IsPosemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomagma : IsPomagma ∙
    assoc     : Associative ∙

  open IsPomagma isPomagma public

  isProsemigroup : IsProsemigroup ∙
  isProsemigroup = record { isPromagma = isPromagma ; assoc = assoc }

  open IsProsemigroup isProsemigroup public using (isSemigroup)

-- Partially ordered monoids (pomonoids)

record IsPomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ∙
    identity      : Identity ε ∙

  open IsPosemigroup isPosemigroup public

  isPromonoid : IsPromonoid ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

  open IsPromonoid isPromonoid public
    using (isMonoid; identityˡ; identityʳ)

-- Partially ordered commutative monoids (commutative pomonoids)

record IsCommutativePomonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    comm       : Commutative ∙

  open IsPomonoid isPomonoid public

  isCommutativePromonoid : IsCommutativePromonoid ∙ ε
  isCommutativePromonoid = record { isPromonoid = isPromonoid ; comm = comm }

  open IsCommutativePromonoid isCommutativePromonoid public
    using (isCommutativeMonoid; isCommutativeSemigroup)

-- Partially ordered semirings (posemirings)

record IsPosemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePomonoid : IsCommutativePomonoid + 0#
    *-mono                  : Monotonic₂ _≲_ _≲_ _≲_ *
    *-assoc                 : Associative *
    *-identity              : Identity 1# *
    distrib                 : * DistributesOver +
    zero                    : Zero 0# *

  open IsCommutativePomonoid +-isCommutativePomonoid public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; mono                   to +-mono
    ; mono₁                  to +-mono₁
    ; mono₂                  to +-mono₂
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isPromagma             to +-isPromagma
    ; isPomagma              to +-isPomagma
    ; isSemigroup            to +-isSemigroup
    ; isProsemigroup         to +-isProsemigroup
    ; isPosemigroup          to +-isPosemigroup
    ; isMonoid               to +-isMonoid
    ; isPromonoid            to +-isPromonoid
    ; isPomonoid             to +-isPomonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativePromonoid to +-isCommutativePromonoid
    )

  *-isPomonoid : IsPomonoid * 1#
  *-isPomonoid = record
    { isPosemigroup      = record
      { isPomagma        = record
        { isPartialOrder = isPartialOrder
        ; mono           = *-mono
        }
      ; assoc            = *-assoc
      }
    ; identity           = *-identity
    }

  open IsPomonoid *-isPomonoid public
    using ()
    renaming
    ( ∙-cong         to *-cong
    ; ∙-congˡ        to *-congˡ
    ; ∙-congʳ        to *-congʳ
    ; mono₁          to *-mono₁
    ; mono₂          to *-mono₂
    ; identityˡ      to *-identityˡ
    ; identityʳ      to *-identityʳ
    ; isMagma        to *-isMagma
    ; isPromagma     to *-isPromagma
    ; isPomagma      to *-isPomagma
    ; isSemigroup    to *-isSemigroup
    ; isProsemigroup to *-isProsemigroup
    ; isPosemigroup  to *-isPosemigroup
    ; isMonoid       to *-isMonoid
    ; isPromonoid    to *-isPromonoid
    )

  isProsemiring : IsProsemiring + * 0# 1#
  isProsemiring = record
    { +-isCommutativePromonoid = +-isCommutativePromonoid
    ; *-cong                   = *-cong
    ; *-mono                   = *-mono
    ; *-assoc                  = *-assoc
    ; *-identity               = *-identity
    ; distrib                  = distrib
    ; zero                     = zero
    }

  open IsProsemiring isProsemiring public
    using (isSemiring; distribˡ; distribʳ; zeroˡ; zeroʳ) 

------------------------------------------------------------------------------
-- Residuated monoids

record IsResiduatedPromonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPromonoid : IsPromonoid ∙ ε
    residuated  : Residuated ∙ ⇦ ⇨

  open IsPromonoid isPromonoid public

  residualˡ : LeftResidual ∙ ⇦
  residualˡ = proj₁ residuated

  residualʳ : RightResidual ∙ ⇨
  residualʳ = proj₂ residuated

record IsResiduatedCommutativePromonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePromonoid : IsCommutativePromonoid ∙ ε
    residualʳ              : RightResidual ∙ ⇨

  open IsCommutativePromonoid isCommutativePromonoid public

  residualˡ : LeftResidual ∙ (flip ⇨)
  residualˡ x y z .Function.Equivalence.to x∙y≲z = 
    residualʳ y x z .Function.Equivalence.to (≲-respˡ-≈ (comm x y) x∙y≲z)
  residualˡ x y z .Function.Equivalence.from y≲z⇦x =
    ≲-respˡ-≈ (comm y x) (residualʳ y x z .Function.Equivalence.from y≲z⇦x)
  residualˡ x y z .Function.Equivalence.to-cong PropEq.refl = PropEq.refl
  residualˡ x y z .Function.Equivalence.from-cong PropEq.refl = PropEq.refl

  residuated : Residuated ∙ (flip ⇨) ⇨
  residuated = residualˡ , residualʳ

  eval : ∀ x y → ∙ x (⇨ x y) ≲ y
  eval x y = residualˡ x (⇨ x y) y .Function.Equivalence.from refl

  ⇨-antitonic-monotonic : AntitonicMonotonic _≲_ _≲_ _≲_ ⇨
  ⇨-antitonic-monotonic x≲w y≲z =
    residualʳ _ _ _ .Function.Equivalence.to 
      (trans (mono refl x≲w) (trans (trans ((≲-respˡ-≈ (comm _ _) refl)) (eval _ _)) y≲z))

record IsResiduatedPomonoid (∙ ⇦ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPomonoid : IsPomonoid ∙ ε
    residuated : Residuated ∙ ⇦ ⇨

  open IsPomonoid isPomonoid public

record IsResiduatedCommutativePomonoid (∙ ⇨ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCommutativePomonoid : IsCommutativePomonoid ∙ ε
    residualʳ              : RightResidual ∙ ⇨

  open IsCommutativePomonoid isCommutativePomonoid public

  isResiduatedCommutativePromonoid : IsResiduatedCommutativePromonoid ∙ ⇨ ε
  isResiduatedCommutativePromonoid = record
    { isCommutativePromonoid = isCommutativePromonoid
    ; residualʳ              = residualʳ
    }

  open IsResiduatedCommutativePromonoid isResiduatedCommutativePromonoid public
    using (residualˡ; residuated)

------------------------------------------------------------------------------
-- Residuated monoids

import Algebra.Definitions _≲_        as ≲
import Algebra.Definitions (flip _≲_) as ≳

record IsDuoidal (∙ ▷ : Op₂ A) (ε ι : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    ∙-isPomonoid   : IsPomonoid ∙ ε
    ▷-isPomonoid   : IsPomonoid ▷ ι
    ∙-▷-exchange   : Exchange ∙ ▷
    ∙-idempotent-ι : ∙ ≲.IdempotentOn ι
    ▷-idempotent-ε : ▷ ≳.IdempotentOn ε
    ε≲ι            : ε ≲ ι
 