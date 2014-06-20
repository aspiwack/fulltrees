
val has_some : 'a option -> bool

exception IsNone
val get : 'a option -> 'a

val map : ('a -> 'b) -> 'a option -> 'b option

val default : 'a -> 'a option -> 'a

val cons : 'a option -> 'a list -> 'a list

val flatten : 'a option list -> 'a list
