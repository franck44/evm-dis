
object "Runtime" {
    code {
  
    function max(x) -> result 
    {
        if eq(x, 2) {
            result := x
        }
    }
    // let x := 8
    // let y := 3
    // let z := 10
    let r := max(2)
    r := max(3)
  
    mstore(0x40, r)
    return(0x40, 32)
    }
  }
  