
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

  for { let k := 0 } lt(k, 10) { } {
    let h := mul(k, 2)
    z := max(z, h )
  }

  mstore(0x40, z)
  return(0x40, 32)
  }
}
