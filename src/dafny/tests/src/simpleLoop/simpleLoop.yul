
object "Runtime" {
  code {

    // let i := 0
    // while lt(i, 10) {
    //   i := add(i, 1)
    // }
    let r := 0
    for { let i := 0 } lt(i, 10) { } {
        r := add(r, 1) 
      }

    mstore(0x40, r)
    return(0x40, 32)

  }
}

