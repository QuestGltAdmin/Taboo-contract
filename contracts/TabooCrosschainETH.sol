// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts-upgradeable/security/ReentrancyGuardUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";

contract TabooCrooschainBuy is Initializable, ReentrancyGuardUpgradeable {

    struct Exchange {
        address userAddress;
        uint256 amountIn;
        uint256 ChainIn;
        uint256 amountOut;
        uint256 timeStamp;
    }

    address public owner;
    address public incommingWallet;

    bool public paused;

    mapping(uint256 => address) exchangeAddress;
    mapping(address => Exchange[]) public UserData;

    modifier priceGreaterThanZero(uint256 _price) {
        require(_price > 0, "Price cannot be 0");
        _;
    }

    modifier onlyOwner() {
        require(owner == msg.sender, "not owner");
        _;
    }

    modifier whenNotPaused() {
        require(!paused, "contract paused");
        _;
    }

    event coinExchange(
        address from,
        address to,
        Exchange exchange
    );

    event Pausable(bool state);

    function initialize(
        address _owner,
        address _incommingWallet
    ) external initializer {
        owner = _owner;
        incommingWallet = _incommingWallet;
    }

    function setWallet(address _owner, address _incommingWallet) external nonReentrant onlyOwner {
        owner = _owner;
        incommingWallet = _incommingWallet;
    }

    function pause(bool _state) external nonReentrant onlyOwner {
        paused = _state;
        emit Pausable(_state);
    }

    function coinTransaction(uint256 _amount) internal {
        (bool success, ) = incommingWallet.call{value: _amount}("");
        require(success, "payment failed");
    }

    function coinPayment(Exchange calldata exchange)
        external
        payable
        priceGreaterThanZero(msg.value)
        whenNotPaused
    {
        require(msg.value >= exchange.amountIn, "amount not enough");

        UserData[msg.sender].push(exchange);

        coinTransaction(msg.value);

        emit coinExchange(msg.sender, incommingWallet, exchange);
    }

    receive() external payable {}
}