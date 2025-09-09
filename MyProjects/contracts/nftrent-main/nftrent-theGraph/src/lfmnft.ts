import { Bytes } from "@graphprotocol/graph-ts";
import { NFTChange as NFTChangeEvent } from "../generated/LFMNFT/LFMNFT";
import { NftInfo } from "../generated/schema";

export function handleNFTChange(event: NFTChangeEvent): void {
  //;
  //let id = Bytes.fromHexString(event.params.tokenId.toHexString());
  let id = event.address.concatI32(event.params.tokenId.toI32());
  let entity = NftInfo.load(id); //new UserNFT();
  if (!entity) {
    entity = new NftInfo(id);
    entity.tokenId = event.params.tokenId;
    entity.ca = event.address;
  }

  entity.owner = event.params.owner;
  entity.tokenURL = event.params.nftUrl;
  entity.blockTimestamp = event.block.timestamp;

  entity.save();
}
