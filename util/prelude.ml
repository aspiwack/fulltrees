open Latex

let rec concat_with_sep a l sep =
  match l with
  | [] -> a
  | b::l -> concat_with_sep (concat [a;sep;b]) l sep

let concat_with_sep l sep =
  match l with
  | [] -> empty
  | a::l -> concat_with_sep a l sep


let nabla = command "nabla" [] M
let implies = command "implies" ~packages:["amsmath",""] [] M

let itshape x = block(unusual_command "itshape" [T,nobr,x] T)
let upalpha = command "upalpha" ~packages:["upgreek",""] [] M
let upbeta = command "upbeta" ~packages:["upgreek",""] [] M
let upgamma = command "upgamma" ~packages:["upgreek",""] [] M
let updelta = command "updelta" ~packages:["upgreek",""] [] M
let upepsilon =  command "upepsilon" ~packages:["upgreek",""] [] M
let upeta = command "upeta" ~packages:["upgreek",""] [] M
let upiota = command "upiota" ~packages:["upgreek",""] [] M
let upmu = command "upmu" ~packages:["upgreek",""] [] M
let uppi = command "uppi" ~packages:["upgreek",""] [] M
let uprho = command "uprho" ~packages:["upgreek",""] [] M
let upsigma = command "upsigma" ~packages:["upgreek",""] [] M
let upomega = command "upomega" ~packages:["upgreek",""] [] M

let log_ = command "log" [] M

let display x =
  displaymath (parbox (`Linewidth 0.9) x)

let vdots = command "vdots" [] A
let module_elipsis =
  let i = 1. in
  let h = 1.5 in
  let debug = false in
  (** /parameters **)
  let h2 = `Baselineskip (h/.2.) in
  let dframe x =
    if debug then framebox (`Width 2.) x
    else x
  in
  hspace (`Em i) ^^
  dframe (raisebox ~shift:(`Ex (-1.)) ~fakeheight:(h2,h2) vdots)

  (* concat [ *)
  (*   hspace (`Em i); *)
  (*   parbox (`Pt 0.) ~valign:`C (rule_ ~lift:(`Baselineskip (-.h/.2.)) (`Pt 1.) (`Baselineskip h) ^^ text"a"); *)
  (*   parbox (`Pt 0.) ~valign:`C (vdots); *)
  (* ] *)

(**** Bibliography ****)
let cite ?extra t =
  let opt =
    match extra with
    | Some x -> Some (T,x)
    | None -> None
  in
  command "cite" ?opt [T,t] T


(*** Holes ***)

let citation_needed = small (text"[citation]")

