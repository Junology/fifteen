import «Fifteen»

open ProofWidgets

def testb : Board 4 4 where
  val := {
    val := #[6,8,11,1,10,5,9,3,7,2,4,13,12,14,0]
    size_eq := by rfl
    nodup := by rewrite [List.toArray_eq_array_mk]; decide
  }
  even := by rfl

#html Board.toHtml {} <| (Board.solved 4 4) |>.applyCyc 0 0 8
#html Board.toHtml {} <| testb
  |>.applyCyc 0 2 (-2)
  |>.applyCyc 1 1 2
  |>.applyCyc 0 2 5
  |>.applyCyc 1 1 5
  |>.applyCyc 1 0 (-3)
  |>.applyCyc 0 0
  |>.applyCyc 2 2 (-1)
  |>.applyCyc 0 1
  |>.applyCyc 2 2
  |>.applyCyc 0 2 4
  |>.applyCyc 1 1 (-1)
  |>.applyCyc 1 2 2
  |>.applyCyc 2 1 2
  |>.applyCyc 1 2 2
  |>.applyCyc 2 2
  |>.applyCyc 1 2 (-1)
  |>.applyCyc 2 2


def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
