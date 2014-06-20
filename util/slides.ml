
module Iterator = struct
  type 'a u =
    | Next of ('a * 'a t)
    | EOI

  and 'a t = 'a u Lazy.t

  let next i =
    match Lazy.force i with
    | Next n -> Some n
    | EOI -> None

  let rec fold f d i =
    match next i with
    | Some (a,i') -> fold f (f a d) i' 
    | None -> d

  let rec from start ~upto =
    if start > upto then
      Lazy.lazy_from_val EOI
    else
      lazy (Next (start , from (start+1) ~upto))

  let rec list l =
    match l with
    | [] -> Lazy.lazy_from_val EOI
    | a::q -> lazy (Next (a , list q))
end


module Frame = struct
  type 'a t = 'a -> Latex.t

  let mk f = f
end


module Slide = struct
  type t = Latex.t * Latex.t list

  let fold_cons f i =
    List.rev (Iterator.fold (fun x a -> (f x)::a) [] i)

  let put i ?(prefix=Latex.empty) f =
    prefix ,
    fold_cons (fun n -> f n) i
end

(* arnaud: il me semble qu'il y a une telle fonction dans latex.ml. Il faudra
   partager le bidule *)

let concat_with_sep l sep =
  if l = [] then
    Latex.empty
  else 
    let l_with_one_too_many = List.flatten (List.map (fun t -> [ sep ; t ]) l) in
    Latex.concat (List.tl l_with_one_too_many)

let null = Latex.command "null" [] Latex.A
let newpage = Latex.concat [ null ; Latex.newpage ]


let unit x = `Cm x
let height = 9.6
let width = 12.80

let document ?prelude ?(packages=[]) slides =
  let slides = 
    List.map begin fun (p,s) ->
      Latex.concat [p;(concat_with_sep s newpage)]
    end slides
  in
  let doc = concat_with_sep slides newpage in
  let geometry =
    Latex.text"geometry",
    Latex.text"papersize={12.80cm,9.60cm},hmargin=0cm,
               vmargin=-0.2cm,
               head=0cm,
               headsep=0pt,
               foot=0cm"
  in
  let packages = geometry::packages in
  Latex.document
    (* mettre la classe Slides ?*)
    ~documentclass:(`Custom "memoir")
    ?prelude
    ~packages
    doc


(*** Destined to latex.ml ***)

open Latex

(* attention, tel quel ça utilise memoir. Pour transvaser dans
   latex.ml, il faudra distribuer [bullet] sur chaque [\item] et abandonner
   spacing…*)
let flist_env name ?(spacing=`Default) ?bullet items =
  let spacing = match spacing with
    | `Default -> empty
    | `Tight -> text"\\tightlist"
    | `Firm -> text"\\firmlist"
  in
  (* Latex produces an error with empty itemize or enumerate. We might as
     well produce the error ourself. *)
  if items = [] then (*arnaud:error*)failwith "itemize or enumerate: no item given";
  let items = List.map (fun (f,x)-> f (text "\\item " ^^ x)) items in
  let items = List.filter (fun x -> not (is_empty x)) items in
  let body = (*concat (arnaud:list_insert*) concat_with_sep items (text "\n")(* )*) in
  let opt = Option.map (fun b -> T,b) bullet in
  environment name ?opt (T, spacing^^body) T

let fitemize = flist_env "itemize"
let fenumerate = flist_env "enumerate"


