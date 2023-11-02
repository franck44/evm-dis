
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
    let z := 10
    let r := max(x, y)
    r := max(r, z)
  
    mstore(0x40, r)
    return(0x40, 32)
    }
  }
  