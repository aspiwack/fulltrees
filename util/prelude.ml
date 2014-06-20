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

(*** Include graphics ***)

let includegraphics ?height ?width ?keepaspectratio t =
  let param k n x = 
    Option.map (fun x -> concat [text n;text"=";k x]) x
  in
  let sparam = param latex_of_size in
  let bparam = param begin function true -> text"true" | false -> text"false" end in
  let width = sparam "width" width in
  let height = sparam "height" height in
  let keepaspectratio = bparam "keepaspectratio" keepaspectratio in
  let opt = A,concat_with_sep (Option.flatten [height;width;keepaspectratio])  (text",") in
  command "includegraphics" ~packages:["graphicx",""] ~opt [A,t] A

(*** Memoir (very incomplete) ***)

let document ?(options=[]) ?(prelude=empty) ?(packages=[]) body =
  let options = (T,concat_with_sep options (text",")) in
  concat [
    documentclass ~opt:options (text"memoir"); par;
    require_packages packages;
    required_packages; par;
    prelude; par;
    documentmatter body;
  ]

let spacing f x =
  environment "Spacing" ~args:[A,latex_of_float f] (T,x) T 

(**** Color *****)

module RgbSet = Map.Make (struct type t = float*float*float let compare = compare end)
let rgbcolors = variable ~eq:(RgbSet.equal (=)) RgbSet.empty
let rgbgensym = variable 0
type color = Latex.t
  let white = text"white"
  let black = text"black"
  let red = text"red"
  let green = text"green"
  let blue = text"blue"
  let magenta = text"magenta"
  let yellow = text"yellow"
  let rgb r g b =
    get rgbcolors (fun s ->
      try
	let name = RgbSet.find (r,g,b) s in
	text name
      with Not_found ->
	get rgbgensym (fun n ->
          let name = "melt-rgb-color-"^(string_of_int n) in
	  set rgbcolors (RgbSet.add (r,g,b) name s)^^
          incr_var rgbgensym^^
          text name)
    )

let color_prelude =
  final rgbcolors begin fun s ->
    RgbSet.fold begin fun (r,g,b) name acc ->
      let rgb = concat [
	latex_of_float r; text",";
	latex_of_float g; text",";
	latex_of_float b]
      in
      command "definecolor" [ A,text name ; A,text"rgb" ; A,rgb ] A
    end s Latex.empty
  end

let color =
  fun c t -> block begin
    unusual_command "color" ~packages:["color",""]
      [A,brace,c ; A,nobr,t] A
  end

(**** Slides ****)

let sffamily x = block(unusual_command "sffamily" [T,nobr,x] T)

let latex_of_float_pair (h,v) =
  concat [ latex_of_float h; text","; latex_of_float v ]

let textblock ?ref_point ~width ~hpos ~vpos x =
  let ref_point = Option.map (fun p -> A,latex_of_float_pair p) ref_point in
  environment "textblock*"
    ~packages:["textpos","absolute"]
    ?opt:ref_point
    ~args:[A,latex_of_size width]
    (A,concat [
      text"(" ; latex_of_size hpos ; text"," ; latex_of_size vpos ; text")" ;
      x
    ])
    A

let ctx_transparent = variable false

let scoped_set v x t =
  get v (fun x' ->
  set v x ^^
  t ^^
  set v x')

let apply ?(braces=false) f ~at t =
  if at then
    f t 
  else if braces then
    within_braces t
  else
    t
let only ~at t =
  if at then t else Latex.empty
let mk_transparent x =
  color white (
    scoped_set ctx_transparent true x
  )
let transparent = apply ~braces:true mk_transparent

let unit = Slides.unit
let height = Slides.height
let width = Slides.width
let logo_size = height/.8.
let header_height = 0.9*.logo_size
let make_logo x = includegraphics ~height:(unit logo_size) (text x)
let coq_logo = "coq_logo.png"
let header_bg = includegraphics ~width:(unit width) ~height:(unit header_height) ~keepaspectratio:false (text"header_bot.png")

let header_background =
  textblock ~width:(unit width) ~hpos:(unit 0.) ~vpos:(unit 0.) header_bg
let header_logo logo =
  textblock ~width:(unit 0.) ~hpos:(unit 0.4) ~vpos:(unit 0.17) (make_logo logo)
let header_title title =
  let offset = 2. in
  textblock ~width:(unit (width -.offset)) ~hpos:(unit offset) ~vpos:(unit (0.25*.header_height))
    (color white (textbf (huge title)))
let header ?logo title =
  let header_logo =
    match logo with
    | None -> empty
    | Some logo -> header_logo logo
  in
  concat [ header_background ; header_logo ; header_title title ]

let frame_body x =
  let vmargin = 0.2 in
  let hmargin = 0.7 in
  let vpos = header_height +. vmargin in
  textblock ~width:(unit (width-. 2.*.hmargin)) ~hpos:(unit hmargin) ~vpos:(unit vpos) begin concat [
    minipage (`Pt 0.) (rule_ (`Pt 0.) (unit (height -. vpos -. vmargin)));
    minipage ~valign:`C (unit (width -. 2.*.hmargin)) (large (sffamily x))
  ] end

let frame ?(logo=coq_logo) ?(title=text"TITLE") f =
  let ff = fun p ->
    concat [
      frame_body (f p) ;
      header ~logo title ;
    ]
  in
  Slides.Frame.mk ff

let title_frame f =
  let ff = fun p ->
    concat [
      frame_body (center (f p)) ;
      header empty ;
    ]
  in
  Slides.Frame.mk ff

let put = Slides.Slide.put
let title_put = Slides.Slide.put

let tighttiny x = spacing 0.6 (tiny x)
