
include "../utils/MiscTypes.dfy"

module {:extern} Expect {

  import opened MiscTypes

  /**
    *   
    */
  function {:extern} verifyProg(x: string): bool

  //   function {:extern} foo2(x: string): Try<bool>


}