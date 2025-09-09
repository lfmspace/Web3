import {
  Transfer as TransferEvent
} from "../generated/templates/S2NFT/S2NFT"
import {
  Transfered
} from "../generated/schema"

export function handleTransfer(event: TransferEvent): void {
  let entity = new Transfered(
    event.transaction.hash.concatI32(event.logIndex.toI32())
  )
  //合约地址
  entity.nftCA = event.address
  //交易发起人
  entity.transFrom = event.transaction.from

  entity.tokenId=event.params.tokenId
  entity.from = event.params.from
  entity.to = event.params.to
  entity.blockNumber = event.block.number
  entity.blockTimestamp = event.block.timestamp
  entity.transactionHash = event.transaction.hash

  entity.save()
}