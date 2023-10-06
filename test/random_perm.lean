import Fifteen.Data.Permutation.Sign
import Fifteen.Data.Permutation.Random

def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => (n+1) * Nat.factorial n

def countDups (as : Array Nat) : Array (Nat × Nat) :=
  let as := as.qsort Nat.blt
  Id.run <| do
    let mut result := #[]
    for n in as do
      if h : result.size = 0 then
        result := result.push (n,1)
      else
        let lst := result.size - 1
        have : lst < result.size := Nat.pred_lt h
        if result[lst].1 = n then
          result := result.modify lst fun x => ⟨x.1,x.2 + 1⟩
        else
          result := result.push (n,1)
    return result

def Permutation.lehmer {n : Nat} (x : Permutation n) : Nat :=
  0 |> x.inversions.foldl fun (k : Nat) (iv : x.Inversion) =>
    k + iv.snd.1.factorial

def test (n : Nat) (fact : Nat := 100) : IO (Array (Nat × Nat)) := do
  let mut lehmers ←
    Nat.foldM
      (fun _ (ls : Array Nat) => do
        let x ← Permutation.randomIO n
        return ls.push x.lehmer
      )
      #[] (fact * n.factorial)
  return countDups lehmers

#eval test 4 1000