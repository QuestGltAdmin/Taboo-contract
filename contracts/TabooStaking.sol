/**
 *Submitted for verification at BscScan.com on 2024-04-11
*/

/**
 *Submitted for verification at BscScan.com on 2024-04-01
 */

// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

/**
 * @dev Interface of the BEP20 standard as defined in the EIP.
 */
interface IBEP20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);

    function isExcluded(address account) external view returns (bool);
}

pragma solidity ^0.8.0;

/**
 * @dev Interface for the optional metadata functions from the BEP20 standard.
 *
 * _Available since v4.1._
 */
interface IBEP20Metadata is IBEP20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

pragma solidity ^0.8.0;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return
            functionCallWithValue(
                target,
                data,
                0,
                "Address: low-level call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        (bool success, bytes memory returndata) = target.call{value: value}(
            data
        );
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data)
        internal
        view
        returns (bytes memory)
    {
        return
            functionStaticCall(
                target,
                data,
                "Address: low-level static call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return
            functionDelegateCall(
                target,
                data,
                "Address: low-level delegate call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage)
        private
        pure
    {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        require(!paused(), "Pausable: paused");
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        require(paused(), "Pausable: not paused");
        _;
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}

contract TabooStaking is ReentrancyGuard, Ownable, Pausable {
    IBEP20 public taboo;
    address public adminIn;
    address public adminOut;
    uint256 oneDay = 86400;
    uint256 oneMonth = 30 * oneDay;
    uint256 public withdrawLimit;
    uint256 public minimumStakeAmount;
    uint256 public stakeCount;
    uint256 public activeStakeCount;
    uint256 public maxAutoRestake;
    uint32 public unstakePeriod;

    struct Stake {
        uint256 deposit;
        uint256 startTime;
        uint256 minLockPeriod;
        uint256 lockMonth;
        uint256 interestRateAPY;
        uint256 interestRateAPR;
        bool active;
        uint256 unstakeDate;
        uint256 interestEarned;
    }

    struct lockingType {
        uint256 month;
        uint256 interestRateAPY;
        uint256 interestRateAPR;
        bool status;
    }

    mapping(address => Stake[]) public stakeData;
    mapping(uint256 => lockingType) public LockingType;

    event stakeEvent(
        address _user,
        uint256 _deposit,
        uint256 _startTime,
        uint256 _lockMonth,
        uint256 _index
    );

    event withdrawEvent(address _user, uint256 _amount, uint256 _index);
    event locktypeAdd(
        uint256 month,
        uint256 interestRateAPY,
        uint256 interestRateAPR,
        bool status
    );
    event changeUnstakePeriod(uint256 unstakePeriod);
    event changeMaxAutoRestake(uint256 maxAutoRestake);
    event changeWithdrawLimit(uint256 withdrawLimit);
    event changeMinimumStake(uint256 minimumStakeAmount);

    constructor(
        IBEP20 _taboo,
        address _adminIn,
        address _adminOut,
        uint256 _withdrawLimit,
        uint256 _minimumStakeAmount,
        uint256 _maxAutoRestake,
        uint32 _unstakePeriod
    ) Pausable() {
        taboo = _taboo;
        adminIn = _adminIn;
        adminOut = _adminOut;
        withdrawLimit = _withdrawLimit;
        unstakePeriod = _unstakePeriod;
        maxAutoRestake = _maxAutoRestake;
        minimumStakeAmount = _minimumStakeAmount;
    }

    function stake(uint256 _amount, uint256 _lockingMonth)
        public
        whenNotPaused
        nonReentrant
    {
        require(
            LockingType[_lockingMonth].status == true,
            "This type of Locking is not availble"
        );

        require(_amount >= minimumStakeAmount, "Less than min stake amt");
        // Get the tokens in the contract
        IBEP20(taboo).transferFrom(msg.sender, adminIn, _amount);
        // Create new entry of deposit
        uint256 _lockingPeriod = (LockingType[_lockingMonth].month) * oneMonth;
        Stake memory _stake;
        _stake.deposit = _amount;
        _stake.startTime = block.timestamp;
        _stake.minLockPeriod = _lockingPeriod;
        _stake.lockMonth = LockingType[_lockingMonth].month;
        _stake.active = true;
        _stake.interestRateAPY = LockingType[_lockingMonth].interestRateAPY;
        _stake.interestRateAPR = LockingType[_lockingMonth].interestRateAPR;
        _stake.interestEarned = 0;
        _stake.unstakeDate = 0;
        stakeData[msg.sender].push(_stake);
        stakeCount = stakeCount + 1;
        activeStakeCount = activeStakeCount + 1;
        uint256 _index = stakeData[msg.sender].length - 1;

        emit stakeEvent(
            msg.sender,
            _amount,
            block.timestamp,
            _lockingMonth,
            _index
        );
    }

    function stakeOwner(
        address _user,
        uint256 _amount,
        uint256 _startTime,
        uint256 _lockingMonth
    ) public nonReentrant onlyOwner {
        require(
            LockingType[_lockingMonth].status == true,
            "This type of Locking is not availble"
        );

        require(_amount >= minimumStakeAmount, "Less than min stake amt");

        // Create new entry of deposit
        uint256 _lockingPeriod = (LockingType[_lockingMonth].month) * oneMonth;

        Stake memory _stake;

        _stake.deposit = _amount;
        _stake.startTime = _startTime;
        _stake.minLockPeriod = _lockingPeriod;
        _stake.lockMonth = LockingType[_lockingMonth].month;
        _stake.interestRateAPY = LockingType[_lockingMonth].interestRateAPY;
        _stake.interestRateAPR = LockingType[_lockingMonth].interestRateAPR;
        _stake.active = true;
        _stake.interestEarned = 0;
        _stake.unstakeDate = 0;

        stakeData[_user].push(_stake);
        stakeCount = stakeCount + 1;
        activeStakeCount = activeStakeCount + 1;
        uint256 _index = stakeData[_user].length - 1;

        emit stakeEvent(_user, _amount, _startTime, _lockingMonth, _index);
    }

    function reStake(
        uint256 _index,
        uint256 _additionalAmt,
        uint256 _lockingMonth
    ) public whenNotPaused nonReentrant {
        Stake memory s = stakeData[msg.sender][_index];

        require(
            LockingType[_lockingMonth].status == true,
            "This type of Locking is not availble"
        );

        require(s.active == true, "Your stake is already withdrawan");

        require(
            (s.startTime + s.minLockPeriod) < block.timestamp,
            "Lock not expired"
        );

        uint256 timeAfterStackEnds = (s.startTime +
            s.minLockPeriod +
            (oneDay * unstakePeriod));
        uint256 timeAfterMaxStack = (s.startTime +
            s.minLockPeriod +
            (s.minLockPeriod * maxAutoRestake));

        if (
            block.timestamp <= timeAfterStackEnds ||
            block.timestamp > timeAfterMaxStack
        ) {
            uint256 tokensEarned = getCompoundInterest(msg.sender, _index);
            uint256 totalWithdrawable = tokensEarned + s.deposit;

            // Get the tokens in the contract
            IBEP20(taboo).transferFrom(msg.sender, adminIn, _additionalAmt);

            stakeData[msg.sender][_index].active = false;
            stakeData[msg.sender][_index].interestEarned = tokensEarned;
            stakeData[msg.sender][_index].unstakeDate = block.timestamp;

            // Create new entry of deposit
            uint256 _lockingPeriod = (LockingType[_lockingMonth].month) *
                oneMonth;
            uint256 _amount = totalWithdrawable + _additionalAmt;

            Stake memory _stake;
            _stake.deposit = _amount;
            _stake.startTime = block.timestamp;
            _stake.minLockPeriod = _lockingPeriod;
            _stake.lockMonth = LockingType[_lockingMonth].month;
            _stake.interestRateAPY = LockingType[_lockingMonth].interestRateAPY;
            _stake.interestRateAPR = LockingType[_lockingMonth].interestRateAPR;
            _stake.active = true;
            _stake.interestEarned = 0;
            _stake.unstakeDate = 0;

            stakeData[msg.sender].push(_stake);
            stakeCount = stakeCount + 1;
            uint256 index = stakeData[msg.sender].length - 1;

            emit stakeEvent(
                msg.sender,
                _amount,
                block.timestamp,
                _stake.lockMonth,
                index
            );
        } else {
            uint256 totalExtraTime = (block.timestamp -
                (s.startTime + s.minLockPeriod));
            uint256 totalExtraDays = totalExtraTime / oneDay;
            uint256 extraRotation = totalExtraDays / (s.lockMonth * 30);

            if (
                totalExtraDays <
                ((s.lockMonth * 30 * extraRotation) + unstakePeriod)
            ) {
                uint256 tokensEarned = getCompoundInterest(msg.sender, _index);
                uint256 totalWithdrawable = tokensEarned + s.deposit;

                // Get the tokens in the contract
                IBEP20(taboo).transferFrom(msg.sender, adminIn, _additionalAmt);

                stakeData[msg.sender][_index].active = false;
                stakeData[msg.sender][_index].interestEarned = tokensEarned;
                stakeData[msg.sender][_index].unstakeDate = block.timestamp;

                // Create new entry of deposit
                uint256 _lockingPeriod = (LockingType[_lockingMonth].month) *
                    oneMonth;
                uint256 _amount = totalWithdrawable + _additionalAmt;

                Stake memory _stake;
                _stake.deposit = _amount;
                _stake.startTime = block.timestamp;
                _stake.minLockPeriod = _lockingPeriod;
                _stake.lockMonth = LockingType[_lockingMonth].month;
                _stake.interestRateAPY = LockingType[_lockingMonth]
                    .interestRateAPY;
                _stake.interestRateAPR = LockingType[_lockingMonth]
                    .interestRateAPR;
                _stake.active = true;
                _stake.interestEarned = 0;
                _stake.unstakeDate = 0;

                stakeData[msg.sender].push(_stake);
                stakeCount = stakeCount + 1;
                uint256 index = stakeData[msg.sender].length - 1;

                emit stakeEvent(
                    msg.sender,
                    _amount,
                    block.timestamp,
                    _stake.lockMonth,
                    index
                );
            } else {
                revert("your stake is Already Auto-Stacked for another period");
            }
        }
    }

    function withdraw(uint256 _index) public whenNotPaused nonReentrant {
        Stake memory s = stakeData[msg.sender][_index];
        require(s.active == true, "Your stake is already withdrawan");

        require(
            (s.startTime + s.minLockPeriod) < block.timestamp,
            "Lock not expired"
        );

        uint256 timeAfterStackEnds = (s.startTime +
            s.minLockPeriod +
            (oneDay * unstakePeriod));
        uint256 timeAfterMaxStack = (s.startTime +
            s.minLockPeriod +
            (s.minLockPeriod * maxAutoRestake));

        if (
            block.timestamp <= timeAfterStackEnds ||
            block.timestamp > timeAfterMaxStack
        ) {
            uint256 tokensEarned = getCompoundInterest(msg.sender, _index);
            uint256 totalWithdrawable = tokensEarned + s.deposit;
            require(
                totalWithdrawable < withdrawLimit,
                "Withdraw Limit cross, please connect to help and support"
            );
            stakeData[msg.sender][_index].active = false;
            stakeData[msg.sender][_index].interestEarned = tokensEarned;
            stakeData[msg.sender][_index].unstakeDate = block.timestamp;

            uint256 AmountTransfer = ((totalWithdrawable * 10416666667) / 1e10);

            if (IBEP20(taboo).isExcluded(msg.sender)) {
                AmountTransfer = totalWithdrawable;
            }

            IBEP20(taboo).transferFrom(adminOut, msg.sender, AmountTransfer);
            activeStakeCount = activeStakeCount - 1;

            emit withdrawEvent(msg.sender, totalWithdrawable, _index);
        } else {
            uint256 totalExtraTime = (block.timestamp -
                (s.startTime + s.minLockPeriod));
            uint256 totalExtraDays = totalExtraTime / oneDay;
            uint256 extraRotation = totalExtraDays / (s.lockMonth * 30);

            if (
                totalExtraDays <
                ((s.lockMonth * 30 * extraRotation) + unstakePeriod)
            ) {
                uint256 tokensEarned = getCompoundInterest(msg.sender, _index);
                uint256 totalWithdrawable = tokensEarned + s.deposit;
                require(
                    totalWithdrawable < withdrawLimit,
                    "Withdraw Limit cross, please connect to help and support"
                );

                stakeData[msg.sender][_index].active = false;
                stakeData[msg.sender][_index].interestEarned = tokensEarned;
                stakeData[msg.sender][_index].unstakeDate = block.timestamp;

                uint256 AmountTransfer = ((totalWithdrawable * 10416666667) /
                    1e10);

                if (IBEP20(taboo).isExcluded(msg.sender)) {
                    AmountTransfer = totalWithdrawable;
                }

                IBEP20(taboo).transferFrom(
                    adminOut,
                    msg.sender,
                    AmountTransfer
                );
                activeStakeCount = activeStakeCount - 1;

                emit withdrawEvent(msg.sender, totalWithdrawable, _index);
            } else {
                revert("your stake is locked for another period");
            }
        }
    }

    function emergencyWithdraw(address _user, uint256 _index)
        public
        nonReentrant
        onlyOwner
    {
        Stake memory s = stakeData[_user][_index];
        require(s.active == true, "Your stake is already withdrawan");
        uint256 tokensEarned = getCompoundInterest(_user, _index);
        uint256 totalWithdrawable = tokensEarned + s.deposit;
        stakeData[_user][_index].active = false;
        stakeData[msg.sender][_index].interestEarned = tokensEarned;
        stakeData[msg.sender][_index].unstakeDate = block.timestamp;
        uint256 AmountTransfer = ((totalWithdrawable * 10416666667) / 1e10);

        if (IBEP20(taboo).isExcluded(_user)) {
            AmountTransfer = totalWithdrawable;
        }
        
        IBEP20(taboo).transferFrom(adminOut, _user, AmountTransfer);

        activeStakeCount = activeStakeCount - 1;
        emit withdrawEvent(_user, totalWithdrawable, _index);
    }

    function getCompoundInterest(address _user, uint256 _index)
        public
        view
        returns (uint256)
    {
        Stake memory s = stakeData[_user][_index];
        uint256 _deposit = s.deposit;
        // duration in sec
        uint256 durationStaked = block.timestamp - s.startTime;
        // duration in day
        durationStaked = durationStaked / oneDay;

        uint256 _interestRate = s.interestRateAPR;

        uint256 withdrawAmount = _deposit;

        for (uint256 i = 1; i <= durationStaked; i++) {
            //oneYear
            uint256 _interestForYear = (withdrawAmount * _interestRate) / 10000;
            //oneDay
            uint256 _interestForDay = _interestForYear / 365;
            withdrawAmount = withdrawAmount + _interestForDay;
        }
        uint256 compoundInterest = withdrawAmount - _deposit;
        return compoundInterest;
    }

    function getStakeData(address _user, uint256 _index)
        public
        view
        returns (
            Stake memory,
            uint256,
            bool,
            uint256,
            uint256
        )
    {
        Stake memory s = stakeData[_user][_index];
        uint256 compoundInterest;
        bool canWithdraw;
        uint256 lastWithdrawDate;
        uint256 NoOfTimeAutoStacked;
        if (s.active) {
            compoundInterest = getCompoundInterest(_user, _index);
            if (block.timestamp < (s.startTime + s.minLockPeriod)) {
                canWithdraw = false;
                lastWithdrawDate = (s.startTime +
                    s.minLockPeriod +
                    (oneDay * unstakePeriod));
            } else {
                if (
                    block.timestamp >
                    (s.startTime +
                        s.minLockPeriod +
                        (s.minLockPeriod * maxAutoRestake))
                ) {
                    canWithdraw = true;
                    lastWithdrawDate = 0;
                    NoOfTimeAutoStacked = maxAutoRestake;
                } else {
                    uint256 totalExtraTime = (block.timestamp -
                        (s.startTime + s.minLockPeriod));
                    uint256 totalExtraDays = totalExtraTime / oneDay;
                    uint256 extraRotation = totalExtraDays / (s.lockMonth * 30);

                    if (
                        totalExtraDays <
                        ((s.lockMonth * 30 * extraRotation) + unstakePeriod)
                    ) {
                        canWithdraw = true;
                        lastWithdrawDate = (s.startTime +
                            s.minLockPeriod +
                            (s.minLockPeriod * extraRotation) +
                            (oneDay * unstakePeriod));
                        NoOfTimeAutoStacked = extraRotation;
                    } else {
                        canWithdraw = false;
                        lastWithdrawDate = (s.startTime +
                            s.minLockPeriod +
                            (s.minLockPeriod * (extraRotation + 1)) +
                            (oneDay * unstakePeriod));
                        NoOfTimeAutoStacked = extraRotation + 1;
                    }
                }
            }
        }
        return (
            s,
            compoundInterest,
            canWithdraw,
            lastWithdrawDate,
            NoOfTimeAutoStacked
        );
    }

    function getStakeLength(address _user) public view returns (uint256) {
        uint256 totalStake = stakeData[_user].length;
        return totalStake;
    }

    function setAdmin(address _adminIn, address _adminOut) public onlyOwner {
        adminIn = _adminIn;
        adminOut = _adminOut;
    }

    function setWithdrawLimit(uint256 _withdrawLimit) public onlyOwner {
        withdrawLimit = _withdrawLimit;
        emit changeWithdrawLimit(_withdrawLimit);
    }

    function setMinimumStaking(uint256 _minimumStakeAmount) public onlyOwner {
        minimumStakeAmount = _minimumStakeAmount;
        emit changeMinimumStake(_minimumStakeAmount);
    }

    function setmaxAutoRestake(uint256 _maxAutoRestake) public onlyOwner {
        maxAutoRestake = _maxAutoRestake;
        emit changeMaxAutoRestake(_maxAutoRestake);
    }

    function setUnstakePeriod(uint32 _unstakePeriod) public onlyOwner {
        unstakePeriod = _unstakePeriod;
        emit changeUnstakePeriod(_unstakePeriod);
    }

    function setStakeStatus(
        address _user,
        uint256 _index,
        bool _status
    ) public onlyOwner {
        stakeData[_user][_index].active = _status;
    }

    function closeMultiStakes(address _user, uint256[] memory _index)
        public
        onlyOwner
    {
        for (uint256 i = 0; i < _index.length; i++) {
            uint256 tokensEarned = getCompoundInterest(_user, _index[i]);
            stakeData[_user][_index[i]].active = false;
            stakeData[msg.sender][_index[i]].interestEarned = tokensEarned;
            stakeData[msg.sender][_index[i]].unstakeDate = block.timestamp;
        }
        activeStakeCount = activeStakeCount - _index.length;
    }

    function changeStakeDate(
        address _user,
        uint256 _index,
        uint256 _startTime
    ) public onlyOwner {
        stakeData[_user][_index].startTime = _startTime;
    }

    function addLockType(
        uint256 _month,
        uint256 _interestRateAPY,
        uint256 _interestRateAPR,
        bool _status
    ) public onlyOwner {
        LockingType[_month].month = _month;
        LockingType[_month].interestRateAPY = _interestRateAPY;
        LockingType[_month].interestRateAPR = _interestRateAPR;
        LockingType[_month].status = _status;

        emit locktypeAdd(_month, _interestRateAPY, _interestRateAPR, _status);
    }
}