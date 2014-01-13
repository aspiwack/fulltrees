val concat_with_sep : Latex.t list -> Latex.t -> Latex.t

val nabla : Latex.t
val implies : Latex.t

val itshape : Latex.t -> Latex.t
val upalpha : Latex.t
val upbeta : Latex.t
val upgamma : Latex.t
val updelta : Latex.t
val upepsilon : Latex.t
val upeta : Latex.t
val upiota : Latex.t
val upmu : Latex.t
val uppi : Latex.t
val uprho : Latex.t
val upsigma : Latex.t
val upomega : Latex.t

val display : Latex.t -> Latex.t

(**** Bibliography ****)
val cite : ?extra:Latex.t -> Latex.t -> Latex.t

(*** Holes ***)

val citation_needed : Latex.t
