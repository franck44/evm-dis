// SPDX-License-Identifier: MIT

pragma solidity >=0.8.0;

contract K {
    bytes name;

    // Claim the throne for the given name by paying the currentClaimFee.
    function updateName(bytes calldata _name) external {
        name = _name;
    }
}
