/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Demos.InteractiveSvg

import Fifteen.Data.Board.Basic


/-!
# HTML elements to depict gameboard
-/


namespace Board

structure Config : Type where
  pieceW : Nat := 40
  pieceH : Nat := 40
  sep : Nat := 5
  fontSize : Nat := 20
  colorBG : String := "grey"
  colorFG : String := "white"
  colorTxt : String := "black"

namespace Config

def get_width (cfg : Config) (n : Nat) : String :=
  (toString <| n * (cfg.pieceW + cfg.sep) + cfg.sep) ++ "px"

def get_height (cfg : Config) (n : Nat) : String :=
  (toString <| n * (cfg.pieceH + cfg.sep) + cfg.sep) ++ "px"

end Config

open ProofWidgets Jsx

def svgElems (cfg : Config) {m n : Nat} (b : Board m n) : Array Html :=
  let frame : Html :=
    <rect
      x="0"
      y="0"
      width={cfg.get_width m}
      height={cfg.get_height n}
      fill={cfg.colorBG}
      stroke={cfg.colorFG} />
  #[frame] |> Nat.fold' (m*n - 1) fun i es =>
    let ix := b.val[i.1].1 % m
    let iy := b.val[i.1] / m
    let x := ix * (cfg.pieceW + cfg.sep) + cfg.sep
    let y := iy * (cfg.pieceH + cfg.sep) + cfg.sep
    let es := es.push <|
      <rect
        x={toString x}
        y={toString y}
        width={toString cfg.pieceW}
        height={toString cfg.pieceH}
        fill={cfg.colorFG} />
    es.push <|
      Html.element "text"
        #[
          ("text-anchor", .str "middle"),
          ("font-size", .str <| toString cfg.fontSize),
          ("x", .str <| toString <| x + cfg.pieceW/2),
          ("y", .str <| toString <| y + cfg.pieceH/2 + cfg.fontSize/3),
          ("stroke", .str "none"),
          ("fill", .str cfg.colorTxt)
        ]
        #[Html.text <| toString <| i.1 + 1]

def toHtml (cfg : Config) {m n : Nat} (b : Board m n) : Html :=
  <div>
    {Html.element "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("version", "1.1"), ("width", .str <| cfg.get_width m), ("height", .str <| cfg.get_height n)] (b.svgElems cfg)}
  </div>

end Board
