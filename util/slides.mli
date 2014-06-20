

module Iterator : sig
  type 'a t

  (* arnaud: on n'en a pas besoin en fait ?
  val next : 'a t -> ('a * 'a t) option

  val fold : ('a -> 'b -> 'b) -> 'b -> 'a t -> 'b *)

  (* *)

  val from : int -> upto:int -> int t

  val list : 'a list -> 'a t
end


module Frame : sig
  type 'a t

  val mk : ('a -> Latex.t) -> 'a t
end


module Slide : sig
  type t

  val put : 'a Iterator.t -> ?prefix:Latex.t -> 'a Frame.t -> t
end

val unit : float -> Latex.size
val height : float
val width : float

val document :
  ?prelude:Latex.t ->
  ?packages:(Latex.t*Latex.t) list ->
  Slide.t list -> Latex.t


(*** Destined to latex.ml ***)

open Latex

val fitemize : ?spacing:[`Default|`Tight|`Firm] -> ?bullet:t -> ((t->t)*t) list -> t
val fenumerate : ?spacing:[`Default|`Tight|`Firm] -> ?bullet:t -> ((t->t)*t) list -> t
