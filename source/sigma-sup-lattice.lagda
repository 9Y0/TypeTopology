Martin Escardo, 15 June 2020

We consider topped σ-sup-lattices. We have ℕ-indexed joins and ⊥ (and
hence finite joins). We also have a top element ⊤.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (*)
open import UF-FunExt
open import UF-Subsingletons

module sigma-sup-lattice
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓤 : Universe)
       where

open import UF-Base
open import UF-SIP
open import UF-Equiv hiding (_≅_)
open import UF-Univalence
open import UF-Subsingletons-FunExt

σ-sup-lattice-structure : 𝓤 ̇ → 𝓤 ̇
σ-sup-lattice-structure X = X × X × ((ℕ → X) → X)

\end{code}

A compatible order for σ-sup-lattice structure (⊤ , ⊥ , ⋁) is a
partial order (prop-valued, reflexive, transitive and antisymmetric
binary relation) such that ⊥ is the smallest element, ⊤ is the largest
element, and ⋁ x is the least upper bound of the sequence x.

\begin{code}

is-σ-sup-compatible-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-σ-sup-compatible-order {𝓥} {X} (⊤ , ⊥ , ⋁) _≤_ =
  ((x y : X) → is-prop (x ≤ y))
             × ((x : X) → x ≤ x)
             × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)
             × ((x y : X) → x ≤ y → y ≤ x → x ≡ y)
             × ((x : X) → x ≤ ⊤)
             × ((x : X) → ⊥ ≤ x)
             × ((x : ℕ → X) (n : ℕ) → x n ≤ ⋁ x)
             × ((x : ℕ → X) (u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u)
\end{code}

We can define the binary sup x ∨ y of two elements x and y by
⋁ (x * y) where x * y is the infinite sequence consisting of x
followed by infinitely many y's. Then we can define the intrinsic
order by x ≤ y iff x ∨ y = y.

\begin{code}

private _*_ : {X : 𝓤 ̇} → X → X → (ℕ → X)
(x * y)       0  = x
(x * y) (succ _) = y

intrinsic-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → (X → X → 𝓤 ̇ )
intrinsic-order (⊤ , ⊥ , ⋁) x y = ⋁ (x * y) ≡ y

syntax intrinsic-order s x y = x ≤[ s ] y

\end{code}

Any compatible order is logically equivalent to the intrinsic order:

\begin{code}

any-σ-sup-order-is-intrinsic-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                                   → is-σ-sup-compatible-order s _≤_
                                   → (x y : X) → x ≤ y ⇔ x ≤[ s ] y
any-σ-sup-order-is-intrinsic-order {𝓥} {X} (⊤ , ⊥ , ⋁) _≤_ (≤-prop-valued , ≤-refl , ≤-trans , ≤-anti , top , bottom , ⋁-is-ub , ⋁-is-lb-of-ubs) x y = a , b
 where
  s = (⊤ , ⊥ , ⋁)
  a : x ≤ y → x ≤[ s ] y
  a l = iv
   where
    i :  (n : ℕ) → (x * y) n ≤ y
    i       0  = l
    i (succ n) = ≤-refl y
    ii : ⋁ (x * y) ≤ y
    ii = ⋁-is-lb-of-ubs (x * y) y i
    iii : y ≤ ⋁ (x * y)
    iii = ⋁-is-ub (x * y) (succ 0)
    iv : ⋁ (x * y) ≡ y
    iv = ≤-anti (⋁ (x * y)) y ii iii
  b : x ≤[ s ] y → x ≤ y
  b l = iii
   where
    i : ⋁ (x * y) ≤ y
    i = transport (⋁ (x * y) ≤_) l (≤-refl (⋁ (x * y)))
    ii : x ≤ ⋁ (x * y)
    ii = ⋁-is-ub (x * y) 0
    iii : x ≤ y
    iii = ≤-trans _ _ _ ii i

\end{code}

Therefore, by functional and propositional extensionality, there is at
most one compatible order:

\begin{code}

at-most-one-σ-sup-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ _≤'_ : X → X → 𝓥 ̇ )
                        → is-σ-sup-compatible-order s _≤_
                        → is-σ-sup-compatible-order s _≤'_
                        → _≤_ ≡ _≤'_
at-most-one-σ-sup-order s _≤_ _≤'_ (i , i') (j , j') = γ
 where
  a : ∀ x y → x ≤ y → x ≤' y
  a x y = v ∘ u
   where
    u : x ≤ y → x ≤[ s ] y
    u = lr-implication (any-σ-sup-order-is-intrinsic-order s _≤_ (i , i') x y)
    v : x ≤[ s ] y → x ≤' y
    v = rl-implication (any-σ-sup-order-is-intrinsic-order s _≤'_ (j , j') x y)

  b : ∀ x y → x ≤' y → x ≤ y
  b x y = v ∘ u
   where
    u : x ≤' y → x ≤[ s ] y
    u = lr-implication (any-σ-sup-order-is-intrinsic-order s _≤'_ (j , j') x y)
    v : x ≤[ s ] y → x ≤ y
    v = rl-implication (any-σ-sup-order-is-intrinsic-order s _≤_ (i , i') x y)

  γ : _≤_ ≡ _≤'_
  γ = dfunext fe (λ x → dfunext fe (λ y → pe (i x y) (j x y) (a x y) (b x y)))

\end{code}

Hence being order compatible is property (rather than just data):

\begin{code}

being-σ-sup-order-is-prop : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                          → is-prop (is-σ-sup-compatible-order s _≤_)
being-σ-sup-order-is-prop (⊤ , ⊥ , ⋁) _≤_ = prop-criterion γ
 where
  s = (⊤ , ⊥ , ⋁)
  γ : is-σ-sup-compatible-order s _≤_ → is-prop (is-σ-sup-compatible-order s _≤_)
  γ (≤-prop-valued , ≤-refl , ≤-trans , ≤-anti , top , bottom , ⋁-is-ub , ⋁-is-lb-of-ubs) =
    ×₈-is-prop (Π₂-is-prop fe (λ x y → being-prop-is-prop fe))
               (Π-is-prop  fe (λ x → ≤-prop-valued x x))
               (Π₅-is-prop fe (λ x _ z _ _ → ≤-prop-valued x z))
               (Π₄-is-prop fe (λ x y _ _ → type-with-prop-valued-refl-antisym-rel-is-set
                                            _≤_ ≤-prop-valued ≤-refl ≤-anti))
               (Π-is-prop  fe (λ x → ≤-prop-valued x ⊤))
               (Π-is-prop  fe (λ x → ≤-prop-valued ⊥ x))
               (Π₂-is-prop fe (λ x n → ≤-prop-valued (x n) (⋁ x)))
               (Π₃-is-prop fe (λ x u _ → ≤-prop-valued (⋁ x) u))
\end{code}

The σ-sup-lattice axiom says that there exists a compatible order,
which is then unique by the above:

\begin{code}

σ-sup-lattice-axiom : (𝓥 : Universe) {X : 𝓤 ̇ } → σ-sup-lattice-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
σ-sup-lattice-axiom 𝓥 {X} s = Σ _≤_ ꞉ (X → X → 𝓥 ̇ ) , (is-σ-sup-compatible-order s _≤_)

σ-sup-lattice-axiom-gives-is-set : {X : 𝓤 ̇ } {s : σ-sup-lattice-structure X}
                                 → σ-sup-lattice-axiom 𝓥 s → is-set X
σ-sup-lattice-axiom-gives-is-set (_≤_ , ≤-prop-valued , ≤-refl , _ , ≤-anti , _) =
  type-with-prop-valued-refl-antisym-rel-is-set _≤_ ≤-prop-valued ≤-refl ≤-anti


σ-sup-lattice-axiom-is-prop : {𝓥 : Universe}
                             → {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X)
                             → is-prop (σ-sup-lattice-axiom 𝓥 {X} s)
σ-sup-lattice-axiom-is-prop s (_≤_ , a) (_≤'_ , a') = to-subtype-≡
                                                        (being-σ-sup-order-is-prop s)
                                                        (at-most-one-σ-sup-order s _≤_ _≤'_ a a')

σ-Sup-Lattice : (𝓥  : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
σ-Sup-Lattice 𝓥 = Σ X ꞉  𝓤 ̇ , Σ s ꞉ σ-sup-lattice-structure X , σ-sup-lattice-axiom 𝓥 s

open sip

σ-Sup-Lattice-underlying-order-is-set : (L : σ-Sup-Lattice 𝓥) → is-set ⟨ L ⟩
σ-Sup-Lattice-underlying-order-is-set (X , s , a) = σ-sup-lattice-axiom-gives-is-set a

\end{code}
