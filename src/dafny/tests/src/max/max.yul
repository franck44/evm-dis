
object "Runtime" {
  code {

  function max(x, y) -> result 
  {
      result := x
      if lt(x, y) {
          result := y 
      } 
  }
      
  let x := 8

  let y := 3

  let z := max(x, y)

  mstore(0x40, z)
  return(0x40, 32)
  }
}
