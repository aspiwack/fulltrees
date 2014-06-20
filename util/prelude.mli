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

val log_ : Latex.t

val display : Latex.t -> Latex.t

val module_elipsis : Latex.t

(**** Bibliography ****)
val cite : ?extra:Latex.t -> Latex.t -> Latex.t

(*** Holes ***)

val citation_needed : Latex.t

(*** Memoir (very incomplete) ***)

val document : ?options:Latex.t list -> ?prelude:Latex.t
  -> ?packages:(Latex.t*Latex.t) list -> Latex.t -> Latex.t

val spacing : float -> Latex.t -> Latex.t

(**** Color   ****)

type color
  val white : color
  val black : color
  val red : color
  val green : color
  val blue : color
  val magenta : color
  val yellow : color
  val rgb : float -> float -> float -> color
val color : color -> Latex.t -> Latex.t
val color_prelude : Latex.t

(**** Slides  ****)

open Slides

val ctx_transparent : bool Latex.variable

val scoped_set : 'a Latex.variable -> 'a -> Latex.t -> Latex.t

val apply : ?braces:bool -> (Latex.t->Latex.t) -> at:bool -> Latex.t -> Latex.t
val only : at:bool -> Latex.t -> Latex.t
val transparent : at:bool -> Latex.t -> Latex.t

val frame : ?logo:string -> ?title:Latex.t -> ('a -> Latex.t) -> 'a Frame.t
val title_frame : ('a -> Latex.t) -> 'a Frame.t
val put : 'a Iterator.t -> ?prefix:Latex.t -> 'a Frame.t -> Slide.t
val title_put : 'a Iterator.t -> ?prefix:Latex.t -> 'a Frame.t -> Slide.t

val tighttiny : Latex.t -> Latex.t





