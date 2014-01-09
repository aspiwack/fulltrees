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

let display x =
  displaymath (parbox (`Linewidth 0.7) x)

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

