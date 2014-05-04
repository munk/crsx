module "edu.nyu.cims.cc.Check" {
// \url{http://cs.nyu.edu/courses/spring14/CSCI-GA.2130-001/check.hx}

// PARSER.

space [ \t\n] ;
token INT      | [0-9]+ ;
token FLOAT    | [0-9]+ [.] [0-9]* ([Ee] [-+]? [0-9]+)? ;
token ID       | [a-z] [a-zA-Z0-9_]* ;
sort Name | symbol ⟦⟨ID⟩⟧ ;

sort S  | ⟦ ⟨[x:Name]⟩ := ⟨E⟩; ⟨S[x:Name]⟩ ⟧ | ⟦ { ⟨S⟩ } ⟨S⟩ ⟧
	| ⟦ printInt ⟨E⟩; ⟨S⟩ ⟧ | ⟦ printFloat ⟨E⟩; ⟨S⟩ ⟧
	| ⟦⟧ ;

sort E 	| ⟦ ⟨E⟩ + ⟨E@1⟩ ⟧ | ⟦ ⟨E@1⟩ * ⟨E@2⟩ ⟧@1 | ⟦ ⟨INT⟩ ⟧@2 | ⟦ ⟨FLOAT⟩ ⟧@2 | ⟦ ⟨Name⟩ ⟧@2
     	| sugar ⟦ ( ⟨E#1⟩ ) ⟧@2 → E#1 ;

// SEMANTIC SORTS \& HELPERS.

sort Bool | ⟦T⟧ | ⟦F⟧;
| scheme ⟦⟨Bool⟩∧⟨Bool⟩⟧;  ⟦T∧T⟧ → ⟦T⟧;  default ⟦⟨Bool#1⟩∧⟨Bool#2⟩⟧ → ⟦F⟧;

sort Type | Int | Float | TypeError;
| scheme Unif(Type,Type);
Unif(Int, Int) → Int;      Unif(Int, Float) → Float;
Unif(Float, Int) → Float;  Unif(Float, Float) → Float;
default Unif(#1, #2) → TypeError ;

sort Bool;
| scheme IsType(Type);  IsType(Int) → ⟦T⟧;  IsType(Float) → ⟦T⟧;  IsType(TypeError) → ⟦F⟧;
| scheme CheckInt(Type);  CheckInt(Int) → ⟦T⟧;  default CheckInt(#) → ⟦F⟧;
| scheme CheckFloat(Type);  CheckFloat(Float) → ⟦T⟧;  default CheckFloat(#) → ⟦F⟧;

// TYPE CHECKING.

sort CheckResult | ⟦Yes⟧;
| scheme Check(S) ;
Check(#s↑ok(⟦T⟧)) → ⟦Yes⟧ ;
Check(#s↑ok(⟦F⟧)) → error⟦Type Error.⟧ ;

// Attributes.
attribute ↑ok(Bool);
attribute ↑t(Type);
attribute ↓e{Name:Type};

// Rules for $S$ sort:
// -- Synthesizes attribute $ok$.
// -- Inherited attribute $S.e$ is distributed by Te scheme (and helper Te2).
sort S | ↑ok | scheme ⟦Te ⟨S⟩⟧ ↓e | scheme ⟦Te2 ⟨S⟩⟧ ↓e ;

// $(S1)\quad S→\textbf{name}:=E_1;S_2$ has three stages:
// 1. $E_1.e = S.e$ and recurse over $E_1$ (to get automatic propagation).
⟦ Te x := ⟨E#1⟩; ⟨S#2[x]⟩ ⟧  →  ⟦ Te2 x := Te⟨E#1⟩; ⟨S#2[x]⟩ ⟧ ;
// 2. When $E_1.t$ is available then $S_2.e = \op{extend}(S.e, \textbf{name}.sym, E_1.t)$ and recurse over $S_2$.
⟦ Te2 x := ⟨E#1↑t(#t1)⟩; ⟨S#2[x]⟩ ⟧  →  ⟦ x := ⟨E#1⟩; Te⟨S#2[x]↓e{x:#t1}⟩ ⟧ ;
// 3. When $S_2.ok$ is (also) available then we can synthesize $S.ok = \op{IsType}(E_1.t) ∧ S_2.ok$.
⟦ x := ⟨E#1↑t(#t1)⟩; ⟨S#2[x]↑ok(#ok2)⟩ ⟧ ↑ok(⟦⟨Bool IsType(#t1)⟩∧⟨Bool#ok2⟩⟧) ;

// $(S2)\quad S→\{S_1\}\,S_2$:
// 1. $S_1.e=S.e$ and $S_2.e=S.e$ are propagated and recursed over.
⟦ Te { ⟨S#1⟩ } ⟨S#2⟩ ⟧  →  ⟦ { Te⟨S#1⟩ } Te⟨S#2⟩ ⟧ ;
// 2. When $S_1.ok$ and $S_2.ok$ are available then synthesize $S.ok=S_1.ok∧S_2.ok$.
⟦ { ⟨S#1↑ok(#ok1)⟩ } ⟨S#2↑ok(#ok2)⟩ ⟧ ↑ok(⟦⟨Bool#ok1⟩ ∧ ⟨Bool#ok2⟩⟧) ;

// $(S3)\quad S→\op{printInt}\,E_1; S_2$:
// 1. $E_1.e=S.e$ and $S_2.e=S.e$ are propagated and recursed over.
⟦ Te printInt ⟨E#1⟩; ⟨S#2⟩ ⟧  →  ⟦ printInt Te⟨E#1⟩; Te⟨S#2⟩ ⟧ ;
// 2. When $S_1.t$ and $S_2.ok$ are available then synthesize $S.ok=\op{Check}(\op{Int}=E_1.t) ∧ S_2.ok$.
⟦ printInt ⟨E#1↑t(#t1)⟩; ⟨S#2↑ok(#ok2)⟩ ⟧ ↑ok(⟦ ⟨Bool CheckInt(#t1)⟩ ∧ ⟨Bool#ok2⟩ ⟧) ;

// $(S4)\quad S→\op{printFloat}\,E_1; S_2$:
// 1. $E_1.e=S.e$ and $S_2.e=S.e$ are propagated and recursed over.
⟦ Te printFloat ⟨E#1⟩; ⟨S#2⟩ ⟧  →  ⟦ printFloat Te⟨E#1⟩; Te⟨S#2⟩ ⟧ ;
// 2. When $S_1.t$ and $S_2.ok$ are available then synthesize $S.ok=\op{Check}(\op{Float}=E_1.t) ∧ S_2.ok$.
⟦ printFloat ⟨E#1↑t(#t1)⟩; ⟨S#2↑ok(#ok2)⟩ ⟧ ↑ok(⟦ ⟨Bool CheckFloat(#t1)⟩ ∧ ⟨Bool#ok2⟩ ⟧) ;

// $(S5)\quad S→ε$:
// 1. No distribution necessary.
⟦ Te ⟧  →  ⟦⟧ ;
// 2. Synthesize $S.ok=\op{True}$.
⟦ ⟧ ↑ok(⟦T⟧) ;

// Rules for $E$ sort:
// -- Synthesizes attribute $E.t$.
// -- Inherited attribute $E.e$ is distributed by Te scheme (with helper Te2).
sort E | ↑t | scheme ⟦Te ⟨E⟩⟧ ↓e ;

// $(E1)\quad E→E_1+E_2$:
// 1. $E_1.e=E.e$ and $E_2.e=E.e$ recursively propagated (note use of parenthesis sugar).
⟦ Te ( ⟨E#1⟩ + ⟨E#2⟩ ) ⟧  →  ⟦ (Te⟨E#1⟩) + (Te⟨E#2⟩) ⟧ ;
// 2. When $E_1.t$ and $E_2.t$ available then synthesize $E.t=\op{Unif}(E_1.t,E_2.t)$.
⟦ ⟨E#1↑t(#t1)⟩ + ⟨E#2↑t(#t2)⟩ ⟧ ↑t(Unif(#t1,#t2)) ;

// $(E2)\quad E→E_1*E_2$:
// 1. $E_1.e=E.e$ and $E_2.e=E.e$ recursively propagated (note use of parenthesis sugar).
⟦ Te ( ⟨E#1⟩ * ⟨E#2⟩ ) ⟧  →  ⟦ (Te⟨E#1⟩) * (Te⟨E#2⟩) ⟧ ;
// 2. When $E_1.t$ and $E_2.t$ available then synthesize $E.t=\op{Unif}(E_1.t,E_2.t)$.
⟦ ⟨E#1↑t(#t1)⟩ + ⟨E#2↑t(#t2)⟩ ⟧ ↑t(Unif(#t1,#t2)) ;

// $(E3)\quad E→\t{int}$:
// 1. Propagation leaf: set $E.t=\op{Int}$ directly.
⟦ Te ⟨INT#1⟩ ⟧  →  ⟦ ⟨INT#1⟩ ⟧ ↑t(Int) ;
// 2. Synthesize $E.t=\op{Int}$.
⟦ ⟨INT#1⟩ ⟧ ↑t(Int) ;

// $(E4)\quad E→\t{float}$:
// 1. Propagation leaf: set $E.t=\op{Float}$ directly.
⟦ Te ⟨FLOAT#1⟩ ⟧  →  ⟦ ⟨FLOAT#1⟩ ⟧ ↑t(Float) ;
// 2. Synthesize $E.t=\op{Float}$.
⟦ ⟨FLOAT#1⟩ ⟧ ↑t(Float) ;

//$(E5)\quad S→\t{name}$: There are two disjoint propagation cases:
// a. $\op{defined}(E.e,\t{name}.sym)$ so $E.t=\op{lookup}(E.e,\t{name}.sym)$.
⟦ Te x ⟧ ↓e{x : #t} → ⟦ x ⟧ ↑t(#t) ;
// b. $¬\op{defined}(E.e,\t{name}.sym)$ so $E.t=\op{TypeError}$.
⟦ Te x ⟧ ↓e{¬x} → ⟦ x ⟧ ↑t(TypeError) ;
}
