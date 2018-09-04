Martin Escardo, 2 May 2014.

See remarks below for an explanation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module SquashedSum (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-Embedding
open import GenericConvergentSequence
open import SearchableTypes
open import ConvergentSequenceSearchable (fe U₀ U₀)
open import UF-InjectiveTypes fe
open import ExtendedSumSearchable fe
open import DiscreteAndSeparated
open import UF-SetExamples

fe₀ : funext U₀ U₀
fe₀ = fe U₀ U₀

\end{code}

Recall that the map under : ℕ → ℕ∞ is the natural embedding. Given a
type family X : ℕ → U ̇, we take its right Kan extension
X / under : ℕ∞ → U ̇ and then its sum, which we call the squashed sum
of X and write Σ¹ X. We have that (X / under) ∞ ≃ 𝟙. What is
interesting is that if each X n is searchable then so is Σ¹ X.

\begin{code}

Σ¹ : ∀ {U} → (ℕ → U ̇) → U ̇
Σ¹ X = Σ (X / under)

Σ¹-searchable : ∀ {U} (X : ℕ → U ̇)
             → ((n : ℕ) → searchable(X n))
             → searchable(Σ¹ X)
Σ¹-searchable X ε = extended-sum-searchable
                     under
                     (under-embedding fe₀)
                     ε
                     ℕ∞-searchable

\end{code}

Added 26 July 2018 (implementing ideas of several years ago).

We now develop a discrete (but not searchable) version Σ₁ X of Σ¹ X
with a dense embedding into Σ¹ X, where an embedding is called dense
if the complement of its image is empty. Recall that the function
over𝟙 : ℕ + 𝟙 → ℕ∞ is the natural embedding that maps the isolated
added point to ∞, which is dense.

\begin{code}

over : ℕ → ℕ + 𝟙
over = inl {U₀} {U₀}

over-embedding : is-embedding over
over-embedding = inl-embedding ℕ 𝟙

Σ₁ : ∀ {U} → (ℕ → U ̇) → U ̇
Σ₁ X = Σ (X / over)

under𝟙-over : (n : ℕ) → under𝟙 (over n) ≡ under n
under𝟙-over n = refl

over-discrete : ∀ {U} (X : ℕ → U ̇)
             → ((n : ℕ) → discrete (X n))
             → (z : ℕ + 𝟙) → discrete ((X / over) z)
over-discrete X d (inl n) = retract-discrete-discrete
                             (equiv-retract-l
                               (Π-extension-in-range X over
                                  over-embedding n))
                             (d n)
over-discrete X d (inr *) = retract-discrete-discrete {U₀}
                             (equiv-retract-l
                               (Π-extension-out-of-range X over (inr *)
                                   (λ n → +disjoint)))
                             𝟙-discrete

Σ₁-discrete : ∀ {U} (X : ℕ → U ̇)
           → ((n : ℕ) → discrete(X n))
           → discrete (Σ₁ X)
Σ₁-discrete X d = Σ-discrete
                    (+discrete ℕ-discrete 𝟙-discrete)
                    (over-discrete X d)

\end{code}

The type (X / over) z is densely embedded into the type
(X / under) (under𝟙 z):

\begin{code}

over-under : ∀ {U} (X : ℕ → U ̇) (z : ℕ + 𝟙)
          → (X / over) z ↪ᵈ (X / under) (under𝟙 z)
over-under X (inl n) = equiv-dense-embedding (
 (X / over) (over n)   ≃⟨ Π-extension-in-range X over over-embedding n ⟩
 X n                   ≃⟨ ≃-sym (Π-extension-in-range X under (under-embedding fe₀) n) ⟩
 (X / under) (under n) ■)
over-under X (inr *) = equiv-dense-embedding (
 (X / over) (inr *) ≃⟨ Π-extension-out-of-range X over (inr *) (λ x → +disjoint ) ⟩
 𝟙 {U₀}             ≃⟨ ≃-sym (Π-extension-out-of-range X under ∞ (λ n p → ∞-is-not-ℕ n (p ⁻¹))) ⟩
 (X / under) ∞      ■ )

over-under-map : ∀ {U} (X : ℕ → U ̇) (z : ℕ + 𝟙)
              → (X / over) z → (X / under) (under𝟙 z)
over-under-map X z = detofun (over-under X z)

over-under-map-left : ∀ {U} (X : ℕ → U ̇) (n : ℕ)
                     (φ : (w : fiber over (inl n)) → X (pr₁ w))
                   → over-under-map X (inl n) φ (n , refl)
                   ≡ φ (n , refl)
over-under-map-left X n φ =
 transport
  (λ - → over-under-map X (inl n) φ (n , refl)
       ≡ transport (λ - → X (pr₁ -)) - (φ (n , refl)))
  (prop-is-set
    (under-embedding fe₀ (under n))
    (under-embedding fe₀ (under n) (n , refl) (n , refl))
    refl)
  (f (n , refl))
 where
  -- We define this for the sake of clarity only:
  f : (t : fiber under (under n))
    → over-under-map X (inl n) φ t
    ≡ transport (λ - → X (pr₁ -))
                 (under-embedding fe₀ (under n) (n , refl) t)
                 (φ (n , refl))
  f t = refl

over-under-map-dense : ∀ {U} (X : ℕ → U ̇) (z : ℕ + 𝟙)
                    → is-dense (over-under-map X z)
over-under-map-dense X z = is-dense-detofun (over-under X z)

\end{code}

The discrete type Σ₁ X is densely embedded into
the searchable type Σ¹ X:

\begin{code}

Σ-up : ∀ {U} (X : ℕ → U ̇) → Σ₁ X → Σ¹ X
Σ-up X = pair-fun under𝟙 (over-under-map X)

Σ-up-embedding : ∀ {U} (X : ℕ → U ̇) → is-embedding (Σ-up X)
Σ-up-embedding X = pair-fun-embedding
                    under𝟙
                    (over-under-map X)
                    (under𝟙-embedding fe₀)
                    (λ z → is-embedding-detofun (over-under X z))

Σ-up-dense : ∀ {U} (X : ℕ → U ̇) → is-dense (Σ-up X)
Σ-up-dense X = pair-fun-dense under𝟙
                (over-under-map X)
                (under𝟙-dense fe₀)
                (λ z → is-dense-detofun (over-under X z))

\end{code}

But this is not enough: we need a map Σ↑ : Σ₁ X → Σ¹ Y given maps f n
: X n → Y n, which has to preserve dense embeddings.

\begin{code}

Over : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
       (f : (n : ℕ) → X n → Y n)
    → (z : ℕ + 𝟙) → (X / over) z → (Y / over) z
Over X Y f (inl n) =
  eqtofun (≃-sym (Π-extension-in-range Y over over-embedding n)) ∘
  f n ∘
  eqtofun (Π-extension-in-range X over over-embedding n)
Over X Y f (inr *) =
  _∘_ {_} {U₀}
   (eqtofun (≃-sym (Π-extension-out-of-range Y over (inr *) (λ _ → +disjoint))))
   (eqtofun (Π-extension-out-of-range X over (inr *) (λ _ → +disjoint)))

Over-inl : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇) (f : (n : ℕ) → X n → Y n)
    → (n : ℕ) → Over X Y f (inl n)
    ≡ λ (φ : (X / over) (inl n)) (w : fiber over (inl n)) →
         transport (λ - → Y (pr₁ -))
                   (inl-embedding ℕ 𝟙 (inl n) (n , refl) w)
                   (f n (φ (n , refl)))
Over-inl X Y f n = refl

Over-inr : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇) (f : (n : ℕ) → X n → Y n)
        → Over X Y f (inr *) ≡ λ φ w → 𝟘-elim (+disjoint (pr₂ w))
Over-inr X Y f = refl

\end{code}

The following two proofs look complicated, but are rather simple:
composition preserves dense maps and embeddings, and equivalences are
dense embeddings.

\begin{code}

Over-dense : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
             (f : (n : ℕ) → X n → Y n)
          → ((n : ℕ) → is-dense (f n))
          → (z : ℕ + 𝟙) → is-dense (Over X Y f z)
Over-dense X Y f d (inl n) =
 comp-dense
  (comp-dense
    (is-equiv-is-dense (eqtofun (Π-extension-in-range X over over-embedding n))
     (is-equiv-eqtofun (Π-extension-in-range X over over-embedding n)))
    (d n))
  (is-equiv-is-dense (eqtofun (≃-sym (Π-extension-in-range Y over over-embedding n)))
   (is-equiv-eqtofun (≃-sym (Π-extension-in-range Y over over-embedding n))))
Over-dense X Y f d (inr *) =
 comp-dense {_} {U₀}
  (is-equiv-is-dense (eqtofun (Π-extension-out-of-range X over (inr *) (λ x → +disjoint)))
   (is-equiv-eqtofun (Π-extension-out-of-range X over (inr *) (λ x → +disjoint))))
  (is-equiv-is-dense (eqtofun (≃-sym (Π-extension-out-of-range Y over (inr *) (λ x → +disjoint))))
   (is-equiv-eqtofun (≃-sym (Π-extension-out-of-range Y over (inr *) (λ x → +disjoint)))))

Over-embedding : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
                 (f : (n : ℕ) → X n → Y n)
              → ((n : ℕ) → is-embedding (f n))
              → (z : ℕ + 𝟙) → is-embedding (Over X Y f z)
Over-embedding {U} X Y f d (inl n) =
 comp-embedding
  (comp-embedding
    (is-equiv-is-embedding (eqtofun (Π-extension-in-range X over over-embedding n))
     (is-equiv-eqtofun (Π-extension-in-range X over over-embedding n)))
    (d n))
  (is-equiv-is-embedding (eqtofun (≃-sym (Π-extension-in-range Y over over-embedding n)))
   (is-equiv-eqtofun (≃-sym (Π-extension-in-range Y over over-embedding n))))
Over-embedding {U} X Y f d (inr *) =
 comp-embedding {U} {U₀}
  (is-equiv-is-embedding (eqtofun (Π-extension-out-of-range X over (inr *) (λ x → +disjoint)))
   (is-equiv-eqtofun (Π-extension-out-of-range X over (inr *) (λ x → +disjoint))))
  (is-equiv-is-embedding (eqtofun (≃-sym (Π-extension-out-of-range Y over (inr *) (λ x → +disjoint))))
   (is-equiv-eqtofun (≃-sym (Π-extension-out-of-range Y over (inr *) (λ x → +disjoint)))))

Σ₁-functor : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇) (f : (n : ℕ) → X n → Y n)
           → Σ₁ X → Σ₁ Y
Σ₁-functor X Y f = pair-fun id (Over X Y f)

Σ₁-functor-dense : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
                   (f : (n : ℕ) → X n → Y n)
                → ((n : ℕ) → is-dense (f n))
                → is-dense (Σ₁-functor X Y f)
Σ₁-functor-dense X Y f d = pair-fun-dense
                            id
                            (Over X Y f)
                            id-is-dense
                            (Over-dense X Y f d)

Σ₁-functor-embedding : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
                       (f : (n : ℕ) → X n → Y n)
                    → ((n : ℕ) → is-embedding (f n))
                    → is-embedding (Σ₁-functor X Y f)
Σ₁-functor-embedding X Y f e = pair-fun-embedding
                                id
                                (Over X Y f)
                                id-is-embedding
                                (Over-embedding X Y f e)

Σ↑ : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
      (f : (n : ℕ) → X n → Y n)
   → Σ₁ X → Σ¹ Y
Σ↑ X Y f = Σ-up Y ∘ Σ₁-functor X Y f

Σ↑-dense : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
            (f : (n : ℕ) → X n → Y n)
         → ((n : ℕ) → is-dense (f n))
         → is-dense (Σ↑ X Y f)
Σ↑-dense X Y f d = comp-dense (Σ₁-functor-dense X Y f d) (Σ-up-dense Y)

Σ↑-embedding : ∀ {U} (X : ℕ → U ̇) (Y : ℕ → U ̇)
               (f : (n : ℕ) → X n → Y n)
            → ((n : ℕ) → is-embedding (f n))
            → is-embedding (Σ↑ X Y f)
Σ↑-embedding X Y f d = comp-embedding (Σ₁-functor-embedding X Y f d) (Σ-up-embedding Y)

\end{code}

We don't need this for the moment:

\begin{code}

under𝟙-over-extension : ∀ {U} {X : ℕ → U ̇} (u : ℕ∞)
                     → ((X / over) / under𝟙) u ≃ (X / under) u
under𝟙-over-extension = iterated-extension over under𝟙

\end{code}

End. What follows is an old version of part of the above.

The original version of the searchability of the squashed sum, given
below was much more convoluted, as it didn't use injective types, but
equivalent, as also shown below.

December 2012, going back to work done circa 2010.

The theorem here is that the "squashed sum" of any countable family of
searchable sets is itself searchable (see the module Searchable,
imported below, for the definition and fundamental facts about the
notion).
open import UF-InjectiveTypes (fe)

(The terminology "squashed sum" comes from the paper "Infinite sets
that satisfy the principle of omniscience in all varieties of
constructive mathematics", where this concept is investigated within
the Cantor type ℕ → ₂, which makes the squashing self-evident.)

Given a countable family of sets.

   X : ℕ → U₀ ̇,

extend it to a ℕ∞-indexed family of sets as follows

  _[_] : (ℕ → U₀ ̇) → (ℕ∞ → U₀ ̇)
  X [ u ] = (k : ℕ) → under k ≡ u → X k

where u ranges over ℕ∞, the one-point compactification of the natural
numbers ℕ, defined in the module GenericConvergentSequence.

The squashed sum of X : ℕ → U₀ ̇ is defined to be

   Σᴵ X = Σ \(u : ℕ∞) → X [ u ]

Intuitively, the squashed sum is the disjoint sum with an added limit
point at infinity.

Assuming excluded middle, Σᴵ X is isomorphic to (Σ \(n : ℕ) → X n) ⊎ 1
where 1 is the one-point type.

Assuming Brouwerian continuity axioms, Σᴵ X is the one-point
compatification of the disjoint sum (Σ \(n : ℕ) → X n).

But we don't assume excluded middle or continuiy axioms here. We work
within intensional MLTT with function extensionality as a postulate
(rather than as a meta-theoretical rule).

\begin{code}

module original-version-and-equivalence-with-new-version where

 _[_] : (ℕ → U₀ ̇) → (ℕ∞ → U₀ ̇)
 X [ u ] = (k : ℕ) → under k ≡ u → X k

 Σᴵ : (ℕ → U₀ ̇) → U₀ ̇
 Σᴵ X = Σ \(u : ℕ∞) → X [ u ]

 ∞₁ : {X : ℕ → U₀ ̇} → Σᴵ X
 ∞₁ = ∞ , λ k r → 𝟘-elim (∞-is-not-ℕ k (r ⁻¹))

\end{code}

 This point at infinity is unique assuming extensionality, because:

\begin{code}

 H : {X : ℕ → U₀ ̇} → (u : ℕ∞) → u ≡ ∞ → (y y' : X [ u ]) → y ≡ y'
 H {X} u r y y' = dfunext fe₀ (λ k → dfunext fe₀ (λ s → lemma k s))
  where
   lemma : (k : ℕ) (s : under k ≡ u) → y k s ≡ y' k s
   lemma k s = 𝟘-elim(∞-is-not-ℕ k (r ⁻¹ ∙ s ⁻¹))

\end{code}

 Next we have an isomorphism X [ u ] ≅ X n if under n ≡ u:

\begin{code}

 F : {X : ℕ → U₀ ̇} (n : ℕ) (u : ℕ∞) → under n ≡ u → X n → X [ u ]
 F {X} n u r x k s = transport X (under-lc (r ∙ s ⁻¹)) x

 G : {X : ℕ → U₀ ̇} (n : ℕ) (u : ℕ∞) → under n ≡ u → X [ u ] → X n
 G n u r y = y n r

 FG : {X : ℕ → U₀ ̇} (n : ℕ) (u : ℕ∞) (r : under n ≡ u) (y : (k : ℕ) → under k ≡ u → X k) → F n u r (G n u r y) ≡ y
 FG {X} n u r y = dfunext fe₀ (λ k → dfunext fe₀ (λ s → lemma k s))
  where
   f : {m n : ℕ} → m ≡ n → X m → X n
   f = transport X

   t : (k : ℕ) → under k ≡ u → n ≡ k
   t k s = under-lc (r ∙ s ⁻¹)

   A :  (n k : ℕ) → n ≡ k → U₀ ̇
   A n k t = (u : ℕ∞) (r : under n ≡ u) (s : under k ≡ u) (y : X [ u ]) → f t (y n r) ≡ y k s

   φ : (n : ℕ) → A n n refl
   φ n = λ u r s y → ap (y n) (ℕ∞-is-set fe₀ r s)

   lemma : (k : ℕ) (s : under k ≡ u) → f (under-lc (r ∙ s ⁻¹)) (y n r) ≡ y k s
   lemma k s = J A φ {n} {k} (t k s) u r s y

 GF : {X : ℕ → U₀ ̇} (n : ℕ) (u : ℕ∞) (r : under n ≡ u) (x : X n) → G {X} n u r (F n u r x) ≡ x
 GF {X} n u r x = s
  where
   f : {m n : ℕ} → m ≡ n → X m → X n
   f = transport X
   claim₀ : f (under-lc (r ∙ r ⁻¹)) x ≡ f (under-lc refl) x
   claim₀ = ap (λ - → f (under-lc -) x) (trans-sym' r)
   claim₁ : f (under-lc refl) x ≡ x
   claim₁ = ap (λ - → f - x) (under-lc-refl n)
   s : f (under-lc (r ∙ r ⁻¹)) x ≡ x
   s = claim₀ ∙ claim₁

\end{code}

 We now can show that the type X [ u ] is searchable for every u : ℕ∞
 provided the type X n is searchable for every n : ℕ. This is tricky,
 because a priory it is not enough to consider the cases under n ≡ u and u ≡ ∞.

 The above isomorphism is used to prove the correctness of the witness
 y₀ below, which is easily defined (using one direction of the
 isomorphism):

\begin{code}

 extension-searchable : {X : ℕ → U₀ ̇} → ((n : ℕ) → searchable(X n)) → (u : ℕ∞) → searchable(X [ u ])
 extension-searchable {X} ε u p = y₀ , lemma
  where
   Y : U₀ ̇
   Y = X [ u ]
   -- ε : (n : ℕ) → searchable(X n)
   -- u : ℕ∞
   -- p  : Y → ₂

   y₀ : Y
   y₀ n r = pr₁(ε n (p ∘ (F n u r)))

   lemma₁ : (n : ℕ) → under n ≡ u → p y₀ ≡ ₁ → (y : Y) → p y ≡ ₁
   lemma₁ n r e = claim₃
    where
     claim₀ : (y : Y) → p(F n u r (G n u r y)) ≡ p y
     claim₀ y = ap p (FG n u r y)
     claim₁ : p(F n u r (G n u r y₀)) ≡ ₁ → (x : X n) → p(F n u r x) ≡ ₁
     claim₁ =  pr₂(ε n (p ∘ (F n u r)))
     claim₂ : (x : X n) → p(F n u r x) ≡ ₁
     claim₂ = claim₁ (claim₀ y₀ ∙ e)
     claim₃ : (y : Y) → p y ≡ ₁
     claim₃ y = (claim₀ y)⁻¹ ∙ claim₂ (G n u r y)

   lemma₂ : u ≡ ∞ → p y₀ ≡ ₁ → (y : Y) → p y ≡ ₁
   lemma₂ r e y = ap p (H u r y y₀) ∙ e

   lemma₁' : p y₀ ≡ ₁ → (y : Y) → p y ≡ ₀ → (n : ℕ) → under n ≢ u
   lemma₁' e y s n r = zero-is-not-one (s ⁻¹ ∙ lemma₁ n r e y)

   lemma₂' : p y₀ ≡ ₁ → (y : Y) → p y ≡ ₀ → u ≢ ∞
   lemma₂' e y s r = zero-is-not-one (s ⁻¹ ∙ lemma₂ r e y)

   lemma : p y₀ ≡ ₁ → (y : Y) → p y ≡ ₁
   lemma r y = Lemma[b≢₀→b≡₁] (λ s → lemma₂' r y s (not-ℕ-is-∞ fe₀ (λ n q → lemma₁' r y s n (q ⁻¹))))

\end{code}

 Finally, we can show that the squashed sum of any sequence of
 searchable sets is itself searchable, as claimed above:

\begin{code}

 Σᴵ-searchable : {X : ℕ → U₀ ̇} → ((n : ℕ) → searchable(X n)) → searchable(Σᴵ X)
 Σᴵ-searchable {X} f = Σ-searchable ℕ∞-searchable (extension-searchable {X} f)

\end{code}

 Added 2 May 2014.

 We show that the old and new squashed sums agree.

\begin{code}

 open import UF-EquivalenceExamples

 agreement-lemma : (X : ℕ → U₀ ̇) (u : ℕ∞)
                → (X / under) u ≃ Π (λ x → under x ≡ u → X x)
 agreement-lemma X = 2nd-Π-extension-formula X under

 agreement : (X : ℕ → U₀ ̇) → Σ¹ X ≃ Σᴵ X
 agreement X = Σ-cong ℕ∞ (X / under) (λ u → X [ u ]) (agreement-lemma X)

\end{code}
