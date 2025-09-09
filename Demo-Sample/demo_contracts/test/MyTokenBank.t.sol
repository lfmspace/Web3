// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import {MyTokenBank} from '../src/Token/MyTokenBank.sol';
import {MyToken} from '../src/Token/MyToken.sol';
import {SigUtils} from '../src/utils/SigUtils.sol';

contract MyTokenBankTest is Test {
    MyToken public token;
    MyTokenBank public tokenBank;
    SigUtils sigUtils;
    uint256 ownerPrivateKey;

    function setUp() public {
        token = new MyToken();
        tokenBank = new MyTokenBank(address(token));
        sigUtils = new SigUtils(token.DOMAIN_SEPARATOR());

        console.log('token is:', address(token));
        console.log('tokenBank is:', address(tokenBank));
        console.log('SigUtils is:', address(sigUtils));
    }

    function testPermitDeposit() public {
        (address owner, uint256 pKey) = makeAddrAndKey('owner');
        ownerPrivateKey = pKey;
        address spender = address(tokenBank);
        SigUtils.Permit memory permit = SigUtils.Permit({
            owner: owner,
            spender: spender,
            value: 100,
            nonce: 0,
            deadline: 1 days
        });
        console.log('owner is:', address(owner));
        console.log('spender is:', address(spender));
        bytes32 digest = sigUtils.getTypedDataHash(permit);

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerPrivateKey, digest);

        vm.startPrank(owner);
        console.log('owner is:', address(owner));
        console.log('spender is:', address(spender));
        console.log('nonce is:', token.nonces(owner));
        token.applyToken(owner);
        tokenBank.permitDeposit(permit.value, permit.deadline, v, r, s);
        assertEq(tokenBank._balances(owner), permit.value);
        vm.stopPrank();
    }
}
