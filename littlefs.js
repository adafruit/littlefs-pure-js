/*********************************************************************/
// LittleFS JavaScript Port based on LittleFS 2.4.2
// Written by Melissa LeBlanc-Williams for Adafruit Industries
/*********************************************************************/

// Error constants
const LFS_ERR_OK          = 0    // No error
const LFS_ERR_IO          = -5   // Error during device operation
const LFS_ERR_CORRUPT     = -84  // Corrupted
const LFS_ERR_NOENT       = -2   // No directory entry
const LFS_ERR_EXIST       = -17  // Entry already exists
const LFS_ERR_NOTDIR      = -20  // Entry is not a dir
const LFS_ERR_ISDIR       = -21  // Entry is a dir
const LFS_ERR_NOTEMPTY    = -39  // Dir is not empty
const LFS_ERR_BADF        = -9   // Bad file number
const LFS_ERR_FBIG        = -27  // File too large
const LFS_ERR_INVAL       = -22  // Invalid parameter
const LFS_ERR_NOSPC       = -28  // No space left on device
const LFS_ERR_NOMEM       = -12  // No more memory available
const LFS_ERR_NOATTR      = -61  // No data/attr available
const LFS_ERR_NAMETOOLONG = -36  // File name too long

const LFS_DISK_VERSION = 0x00020000
const LFS_DISK_VERSION_MAJOR = (0xffff & (LFS_DISK_VERSION >>> 16))
const LFS_DISK_VERSION_MINOR = (0xffff & (LFS_DISK_VERSION >>>  0))

const LFS_NAME_MAX = 32
const LFS_FILE_MAX = 2147483647
const LFS_ATTR_MAX = 1022

const LFS_BLOCK_NULL = -1
const LFS_BLOCK_INLINE = -2

const LFS_TYPE_REG            = 0x001
const LFS_TYPE_DIR            = 0x002

// internally used types
const LFS_TYPE_SPLICE         = 0x400
const LFS_TYPE_NAME           = 0x000
const LFS_TYPE_STRUCT         = 0x200
const LFS_TYPE_USERATTR       = 0x300
const LFS_TYPE_FROM           = 0x100
const LFS_TYPE_TAIL           = 0x600
const LFS_TYPE_GLOBALS        = 0x700
const LFS_TYPE_CRC            = 0x500

// internally used type specializations
const LFS_TYPE_CREATE         = 0x401
const LFS_TYPE_DELETE         = 0x4ff
const LFS_TYPE_SUPERBLOCK     = 0x0ff
const LFS_TYPE_DIRSTRUCT      = 0x200
const LFS_TYPE_CTZSTRUCT      = 0x202
const LFS_TYPE_INLINESTRUCT   = 0x201
const LFS_TYPE_SOFTTAIL       = 0x600
const LFS_TYPE_HARDTAIL       = 0x601
const LFS_TYPE_MOVESTATE      = 0x7ff

// internal chip sources
const LFS_FROM_NOOP = 0x000
const LFS_FROM_MOVE = 0x101
const LFS_FROM_USERATTRS = 0x102

// Comparison Constants
const LFS_CMP_EQ = 0
const LFS_CMP_LT = 1
const LFS_CMP_GT = 2

const LFS_F_DIRTY   = 0x010000 // File does not match storage
const LFS_F_WRITING = 0x020000 // File has been written since last flush
const LFS_F_READING = 0x040000 // File has been read since last flush
const LFS_F_ERRED   = 0x080000 // An error occurred during write
const LFS_F_INLINE  = 0x100000 // Currently inlined in directory entry

// File open flags
const LFS_O_RDONLY = 1         // Open a file as read only
const LFS_O_WRONLY = 2         // Open a file as write only
const LFS_O_RDWR   = 3         // Open a file as read and write
const LFS_O_CREAT  = 0x0100    // Create a file if it does not exist
const LFS_O_EXCL   = 0x0200    // Fail if a file already exists
const LFS_O_TRUNC  = 0x0400    // Truncate the existing file to zero size
const LFS_O_APPEND = 0x0800    // Move to end of file on every write

function toHex(value, size=2) {
    return "0x" + value.toString(16).toUpperCase().padStart(size, "0");
}

function toByteArray(str) {
    let byteArray = [];
    for (let i = 0; i < str.length; i++) {
      let charcode = str.charCodeAt(i);
      if (charcode <= 0xFF) {
        byteArray.push(charcode);
      }
    }
    return byteArray;
  }

class LittleFS {
  constructor(config) {
    this.rcache = new Cache();
    this.pcache = new Cache();
    this.root = new Uint8Array(2);
    this.mList = new MList();
    this.seed = 0;
    this.gstate = new GState({tag: 0});
    this.gdisk = new GState({tag: 0});
    this.gdelta = new GState({tag: 0});

    this.free = {
      off: LFS_BLOCK_NULL,
      size: LFS_BLOCK_NULL,
      i: LFS_BLOCK_NULL,
      ack: LFS_BLOCK_NULL,
      buffer: null
    };

    this.nameMax = 0;
    this.fileMax = 0;
    this.attrMax = 0;
    this.init(config);
  }

  init(config) {

    let err = 0;
    if (config) {
      this.cfg = config;
    }

    // validate that the lfs-cfg sizes were initiated properly before
    // performing any arithmetic logics with them
    console.assert(this.cfg.readSize != 0);
    console.assert(this.cfg.progSize != 0);
    console.assert(this.cfg.cacheSize != 0);

    // check that block size is a multiple of cache size is a multiple
    // of prog and read sizes
    console.assert(this.cfg.cacheSize % this.cfg.readSize == 0);
    console.assert(this.cfg.cacheSize % this.cfg.progSize == 0);
    console.assert(this.cfg.blockSize % this.cfg.cacheSize == 0);

    // check that the block size is large enough to fit ctz pointers
    console.assert(4*this.npw2(0xffffffff / (this.cfg.blockSize-2*4))
            <= this.cfg.blockSize);

    // block_cycles = 0 is no longer supported.
    //
    // block_cycles is the number of erase cycles before littlefs evicts
    // metadata logs as a part of wear leveling. Suggested values are in the
    // range of 100-1000, or set block_cycles to -1 to disable block-level
    // wear-leveling.
    console.assert(this.cfg.blockCycles != 0);

    // setup read cache
    if (this.cfg.readBuffer) {
      this.rcache.buffer = this.cfg.readBuffer;
    } else {
      this.rcache.buffer = new Uint8Array(this.cfg.cacheSize);
    }

    // setup program cache
    if (this.cfg.progBuffer) {
      this.pcache.buffer = this.cfg.progBuffer;
    } else {
      this.pcache.buffer = new Uint8Array(this.cfg.cacheSize);
    }

    // zero to avoid information leaks
    this.cacheZero(this.rcache);
    this.cacheZero(this.pcache);

    // setup lookahead, must be multiple of 64-bits, 32-bit aligned
    console.assert(this.cfg.lookaheadSize > 0);
    console.assert(this.cfg.lookaheadSize % 8 == 0 &&
            this.cfg.lookaheadBuffer % 4 == 0);
    if (this.cfg.lookaheadBuffer) {
      this.free.buffer = this.cfg.lookaheadBuffer
    } else {
      this.free.buffer = new Uint8Array(this.cfg.lookaheadSize);
    }

    if (!this.nameMax) {
      this.nameMax = this.cfg.nameMax;
    }

    if (!this.fileMax) {
      this.fileMax = this.cfg.fileMax;
    }

    if (!this.attrMax) {
      this.attrMax = this.cfg.attrMax;
    }

    this.root[0] = LFS_BLOCK_NULL;
    this.root[1] = LFS_BLOCK_NULL;
    this.mList = new MList();
    this.seed = 0;
    this.gdisk.tag = 0;
    this.gstate.tag = 0;
    this.gdelta.tag = 0;
  }

  deinit() {
    if (!this.cfg.readBuffer) {
      this.rcache.buffer = null;
    }

    if (!this.cfg.progBuffer) {
      this.pcache.buffer = null;
    }

    if (!this.cfg.lookaheadBuffer) {
      this.free.buffer = null;
    }
  }

  format() {
    let err;
    main_block: if(true) {
      this.init()
      this.free.off = 0;
      this.free.size = Math.min(this.cfg.lookaheadSize, this.cfg.blockSize)
      this.free.i = 0;
      this.allocAck();
      let root = new MDir();
      err = this.dirAlloc(root);
      if (err) {
        return;
      }
      let superblock = new SuperBlock({
        version: LFS_DISK_VERSION,
        blockSize: this.cfg.blockSize,
        blockCount: this.cfg.blockCount,
        nameMax: this.nameMax,
        fileMax: this.fileMax,
        attrMax: this.attrMax
      });
      this.tagId(0x6000);
      this.superblockTole32(superblock);
      this.dirCommit(root, this.mkAttrs(
        [this.mkTag(LFS_TYPE_CREATE, 0, 0), null],
        [this.mkTag(LFS_TYPE_SUPERBLOCK, 0, 8), "littlefs"],
        [this.mkTag(LFS_TYPE_INLINESTRUCT, 0, struct.calcsize("IIIIII")), superblock]
      ));

      err = this.dirCommit(root, null);

      if (err) {
        break main_block;
      }
      err = this.dirFetch(root, [0, 1]);

      if (err) {
        break main_block;
      }
    }

    this.deinit()
    return err;
  }

  allocAck() {
    this.free.ack = this.cfg.blockCount;
  }

  dirAlloc(dir) {
    let err;
    for (let i = 0; i < 2; i++) {
      let blockObj = new ByRef();
      err = this.alloc(blockObj);
      dir.pair[(i+1) % 2] = blockObj.get();
      if (err) return err;
    }

    dir.rev = 0;

    let bufferByRef = new ByRef(dir.rev)
    err = this.bdRead(null, this.rcache, struct.calcsize("I"), dir.pair[0], 0, bufferByRef, struct.calcsize("I"));
    dir.rev = bufferByRef.get();
    dir.rev = this.fromle32(dir.rev);
    if (err && err != LFS_ERR_CORRUPT) {
      return err;
    }

    if (this.cfg.blockCycles > 0) {
      dir.rev = this.alignup(dir.rev, ((this.cfg.blockCycles+1)|1));
    }

    // set defaults
    dir.off = struct.calcsize("I");
    dir.etag = 0xffffffff;
    dir.count = 0;
    dir.tail[0] = LFS_BLOCK_NULL;
    dir.tail[1] = LFS_BLOCK_NULL;
    dir.erased = false;
    dir.split = false;

    // don't write out yet, let caller take care of that
    return LFS_ERR_OK;
  }

  // Find the smallest power of 2 greater than or equal to a
  npw2(a) {
    let r = 0;
    let s;
    a -= 1;
    s = (a > 0xffff) << 4; a >>>= s; r |= s;
    s = (a > 0xff  ) << 3; a >>>= s; r |= s;
    s = (a > 0xf   ) << 2; a >>>= s; r |= s;
    s = (a > 0x3   ) << 1; a >>>= s; r |= s;
    return (r | (a >>> 1)) + 1;
}

  aligndown(value, alignment) {
    return (value - (value % alignment)) >>> 0;
  }

  alignup(value, alignment) {
    return this.aligndown((value + alignment - 1) >>> 0, alignment);
  }

  alloc(blockObj) {
    while (true) {
        while (this.free.i != this.free.size) {
            let off = this.free.i;
            this.free.i += 1;
            this.free.ack -= 1;
            if (!(this.free.buffer[parseInt(this.free.i / 32)] & (1 << (off % 32)))) {
                // found a free block
                blockObj.set((this.free.off + off) % this.cfg.blockCount);

                // eagerly find next off so an alloc ack can
                // discredit old lookahead blocks
                while (this.free.i != this.free.size &&
                        (this.free.buffer[parseInt(this.free.i / 32)]
                            & (1 << (this.free.i % 32)))) {
                    this.free.i += 1;
                    this.free.ack -= 1;
                }

                return 0;
            }
        }

        // check if we have looked at all blocks since last ack
        if (this.free.ack == 0) {
            console.warn("No more free space " + this.free.i + this.free.off);
            return LFS_ERR_NOSPC;
        }

        this.free.off = (this.free.off + this.free.size)
                % this.cfg.blockCount;
        this.free.size = Math.min(8 * this.cfg.lookaheadSize, this.free.ack);
        this.free.i = 0;

        // find mask of free blocks from tree
        let err = this.fsTraverse(this.allocLookahead.bind(this), null, true);
        if (err) {
            this.allocDrop();
            return err;
        }
    }
  }

  pairIsnull(pair) {
    return pair[0] == LFS_BLOCK_NULL || pair[1] == LFS_BLOCK_NULL;
  }

  fsTraverse(callback, data, includeOrphans) {
    let err;
    // iterate over metadata pairs
    let dir = new MDir();
    dir.tail = [0, 1];

    let cycle = 0;
    while (!this.pairIsnull(dir.tail)) {
        if (cycle >= this.cfg.blockCount/2) {
            // loop detected
            return LFS_ERR_CORRUPT;
        }
        cycle += 1;

        for (let i = 0; i < 2; i++) {
            err = callback(dir.tail[i]);
            if (err) {
                return err;
            }
        }

        // iterate through ids in directory
        err = this.dirFetch(dir, dir.tail);
        if (err) {
            return err;
        }

        for (let id = 0; id < dir.count; id++) {
            let ctz = new Ctz();
            let bufferObj = new ByRef(new Uint8Array(struct.calcsize("II")));
            let tag = this.dirGet(dir, this.mkTag(0x700, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_STRUCT, id, struct.calcsize("II")), bufferObj);
            ctz.setFromBuffer(bufferObj.get())
            if (tag < 0) {
                if (tag == LFS_ERR_NOENT) {
                    continue;
                }
                return tag;
            }
            this.ctzFromle32(ctz);

            if (this.tagType3(tag) == LFS_TYPE_CTZSTRUCT) {
                err = this.ctzTraverse(this.rcache,
                        ctz.head, ctz.size, callback, data);
                if (err) {
                    return err;
                }
            } else if (includeOrphans &&
                    this.tagType3(tag) == LFS_TYPE_DIRSTRUCT) {
                for (let i = 0; i < 2; i++) {
                    err = callback(data, (ctz.head)[i]);
                    if (err) {
                        return err;
                    }
                }
            }
        }
    }

    // iterate over any open files
    for (let f = this.mList; f; f = f.next) {
        if (f.type != LFS_TYPE_REG) {
            continue;
        }

        if ((f.flags & LFS_F_DIRTY) && !(f.flags & LFS_F_INLINE)) {
            let err = this.ctzTraverse(f.cache, this.rcache,
                    f.ctz.head, f.ctz.size, callback, data);
            if (err) {
                return err;
            }
        }

        if ((f.flags & LFS_F_WRITING) && !(f.flags & LFS_F_INLINE)) {
            let err = this.ctzTraverse(f.cache, this.rcache,
                    f.block, f.pos, callback, data);
            if (err) {
                return err;
            }
        }
    }

    return 0;
  }

  dirFetch(dir, pair) {
    // note, mask=-1, tag=-1 can never match a tag since this
    // pattern has the invalid bit set
    return this.dirFetchmatch(dir, pair, -1, -1, new ByRef(null), null, null);
  }

  dirFetchmatch(dir, pair, fmask, ftag, idByRef, callback, data) {
    // we can find tag very efficiently during a fetch, since we're already
    // scanning the entire directory
    let besttag = -1;
    // if either block address is invalid we return LFS_ERR_CORRUPT here,
    // otherwise later writes to the pair could fail
    if (pair[0] >= this.cfg.blockCount || pair[1] >= this.cfg.blockCount) {
        return LFS_ERR_CORRUPT;
    }

    // find the block with the most recent revision
    let revs = [0, 0];
    let r = 0;
    let bufferByRef = new ByRef();
    for (let i = 0; i < 2; i++) {
        let err = this.bdRead(null, this.rcache, struct.calcsize("I"),
                pair[i], 0, bufferByRef, struct.calcsize("I"));
        revs[i] = bufferByRef.get();
        revs[i] = this.fromle32(revs[i]);
        if (err && err != LFS_ERR_CORRUPT) {
            return err;
        }

        if (err != LFS_ERR_CORRUPT &&
                this.scmp(revs[i], revs[(i+1)%2]) > 0) {
            r = i;
        }
    }
    dir.pair[0] = pair[(r+0)%2];
    dir.pair[1] = pair[(r+1)%2];
    dir.rev = revs[(r+0)%2];
    dir.off = 0; // nonzero = found some commits

    // now scan tags to fetch the actual dir and find possible match
    for (let i = 0; i < 2; i++) {
        let off = 0;
        let ptag = 0xffffffff;

        let tempcount = 0;
        let temptail = [LFS_BLOCK_NULL, LFS_BLOCK_NULL];
        let tempsplit = false;
        let tempbesttag = besttag;

        dir.rev = this.tole32(dir.rev);
        let crc = this.crc(0xffffffff, dir.rev, struct.calcsize("I"));
        dir.rev = this.fromle32(dir.rev);

        while (true) {
            // extract next tag
            let tag;
            bufferByRef = new ByRef();
            off += this.tagDsize(ptag);

            let err = this.bdRead(null, this.rcache, this.cfg.blockSize,
                    dir.pair[0], off, bufferByRef, struct.calcsize("I"));
            tag = bufferByRef.get();

            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                    // can't continue?
                    dir.erased = false;
                    break;
                }
                return err;
            }
            crc = this.crc(crc, tag, struct.calcsize("I"));
            tag = (this.fromBe32(tag) ^ ptag) >>> 0;

            // next commit not yet programmed or we're not in valid range
            if (!this.tagIsvalid(tag)) {
                dir.erased = (this.tagType1(ptag) == LFS_TYPE_CRC &&
                        dir.off % this.cfg.progSize == 0);
                break;
            } else if (off + this.tagDsize(tag) > this.cfg.blockSize) {
                dir.erased = false;

                break;
            }

            ptag = tag;

            if (this.tagType1(tag) == LFS_TYPE_CRC) {
                // check the crc attr
                let dcrc;
                bufferByRef = new ByRef();
                err = this.bdRead(null, this.rcache, this.cfg.blockSize,
                        dir.pair[0], off + struct.calcsize("I"), bufferByRef, struct.calcsize("I"));
                if (err) {
                    if (err == LFS_ERR_CORRUPT) {
                        dir.erased = false;
                        break;
                    }
                    return err;
                }
                dcrc = bufferByRef.get();
                dcrc = this.fromle32(dcrc);

                if (crc != dcrc) {
                    dir.erased = false;
                    break;
                }

                // reset the next bit if we need to
                ptag ^= (this.tagChunk(tag) & 1) << 31;
                ptag = ptag >>> 0;

                // toss our crc into the filesystem seed for
                // pseudorandom numbers, note we use another crc here
                // as a collection function because it is sufficiently
                // random and convenient
                this.seed = this.crc(this.seed, crc, struct.calcsize("I"));

                // update with what's found so far
                besttag = tempbesttag;
                dir.off = off + this.tagDsize(tag);
                dir.etag = ptag;
                dir.count = tempcount;
                dir.tail[0] = temptail[0];
                dir.tail[1] = temptail[1];
                dir.split = tempsplit;

                // reset crc
                crc = 0xffffffff;
                continue;
            }

            // crc the entry first, hopefully leaving it in the cache
            for (let j = struct.calcsize("I"); j < this.tagDsize(tag); j++) {
                let dat;
                bufferByRef = new ByRef();
                err = this.bdRead(null, this.rcache, this.cfg.blockSize,
                        dir.pair[0], off+j, bufferByRef, 1);
                if (err) {
                    if (err == LFS_ERR_CORRUPT) {
                        dir.erased = false;
                        break;
                    }
                    return err;
                }
                dat = bufferByRef.get();
                crc = this.crc(crc, dat, 1);
            }

            // directory modification tags?
            if (this.tagType1(tag) == LFS_TYPE_NAME) {
                // increase count of files if necessary
                if (this.tagId(tag) >= tempcount) {
                    tempcount = this.tagId(tag) + 1;
                }
            } else if (this.tagType1(tag) == LFS_TYPE_SPLICE) {
                tempcount += this.tagSplice(tag);
                if (tag == (this.mkTag(LFS_TYPE_DELETE, 0, 0) |
                        (this.mkTag(0, 0x3ff, 0) & tempbesttag))) {
                    tempbesttag |= 0x80000000;
                } else if (tempbesttag != -1 &&
                        this.tagId(tag) <= this.tagId(tempbesttag)) {
                    tempbesttag += this.mkTag(0, this.tagSplice(tag), 0);
                }
            } else if (this.tagType1(tag) == LFS_TYPE_TAIL) {
                tempsplit = (this.tagChunk(tag) & 1);
                bufferByRef = new ByRef();
                err = this.bdRead(null, this.rcache, this.cfg.blockSize,
                        dir.pair[0], off + struct.calcsize("I"), bufferByRef, 8);
                if (err) {
                    if (err == LFS_ERR_CORRUPT) {
                        dir.erased = false;
                        break;
                    }
                }
                temptail = bufferByRef.get();
                this.pairFromle32(temptail);
            }

            // found a match for our fetcher?
            if ((fmask & tag) == (fmask & ftag)) {
                let res = callback(data, tag, new Diskoff({block: dir.pair[0], off: off+struct.calcsize("I")}));
                if (res < 0) {
                    if (res == LFS_ERR_CORRUPT) {
                        dir.erased = false;
                        break;
                    }
                    return res;
                }

                if (res == LFS_CMP_EQ) {
                    // found a match
                    tempbesttag = tag;
                } else if ((this.mkTag(0x7ff, 0x3ff, 0) & tag) ==
                        (this.mkTag(0x7ff, 0x3ff, 0) & tempbesttag)) {
                    // found an identical tag, but contents didn't match
                    // this must mean that our besttag has been overwritten
                    tempbesttag = -1;
                } else if (res == LFS_CMP_GT &&
                        this.tagId(tag) <= this.tagId(tempbesttag)) {
                    // found a greater match, keep track to keep things sorted
                    tempbesttag = tag | 0x80000000;
                }
            }
        }

        // consider what we have good enough
        if (dir.off > 0) {
            // synthetic move
            if (this.gstateHasmovehere(this.gdisk, dir.pair)) {
                if (this.tagId(this.gdisk.tag) == this.tagId(besttag)) {
                    besttag |= 0x80000000;
                } else if (besttag != -1 &&
                        this.tagId(this.gdisk.tag) < this.tagId(besttag)) {
                    besttag -= this.mkTag(0, 1, 0);
                }
            }

            // found tag? or found best id?
            if (idByRef.get()) {
                idByRef.set(Math.min(this.tagId(besttag), dir.count));
            }
            if (this.tagIsvalid(besttag)) {
                return besttag;
            } else if (this.tagId(besttag) < dir.count) {
                return LFS_ERR_NOENT;
            } else {
                return 0;
            }
        }

        // failed, try the other block?
        this.pairSwap(dir.pair);
        dir.rev = revs[(r+1)%2];
    }

    console.warn("Corrupted dir pair at {" +dir.pair[0]+ ", " + dir.pair[1] + "}");
    return LFS_ERR_CORRUPT;
  }

  dirFindMatch(name, tag, disk) {
    // compare with disk
    let diff = Math.min(name.size, this.tagSize(tag));
    let res = this.bdCmp(null, this.rcache, diff,
            disk.block, disk.off, name.name, diff);
    if (res != LFS_CMP_EQ) {
        return res;
    }

    // only equal if our size is still the same
    if (name.size != this.tagSize(tag)) {
        return (name.size < this.tagSize(tag)) ? LFS_CMP_LT : LFS_CMP_GT;
    }

    // found a match!
    return LFS_CMP_EQ;
  }

  allocLookahead(block) {
    let off = ((block - this.free.off) + this.cfg.blockCount) % this.cfg.blockCount
    if (off < this.free.size) {
      let offset = parseInt(off / 32);
      this.free.buffer.set(this.free.buffer.slice(offset, offset + 1) | 1 << (off % 32), offset);
    }
  }

  tagType1(tag) {
    return (tag & 0x70000000) >>> 20;
  }

  tagType3(tag) {
    return (tag & 0x7ff00000) >>> 20;
  }

  tagId(tag) {
    return (tag & 0x000ffc00) >>> 10;
  }

  tagDsize(tag) {
    return struct.calcsize("I") + this.tagSize(tag + this.tagIsdelete(tag));
  }

  tagSize(tag) {
    return tag & 0x000003ff;
  }

  tagIsdelete(tag) {
    return ((tag << 22) >> 22) == -1;
  }

  tagIsvalid(tag) {
    return !(tag & 0x80000000);
  }

  tagChunk(tag) {
    return ((tag & 0x0ff00000) >> 20) & 0xff;
  }

  tagSplice(tag) {
    return (this.tagChunk(tag) << 24) >> 24;
  }

  crc(crc, buffer, size) {
    let data;
    const rtable = [
        0x00000000, 0x1db71064, 0x3b6e20c8, 0x26d930ac,
        0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c,
        0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c,
        0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c,
    ];

    if (buffer == null) {
      data = [];
    } else if (typeof buffer === 'string') {
      data = toByteArray(buffer);
    } else if (typeof buffer === 'object') {
      data = new Uint8Array(size);
      const dataSize = parseInt(size / Object.entries(buffer).length);
      Object.values(buffer).forEach((value, index) => {
        data.set(LittleFS.UintToBuffer(value, dataSize), index * dataSize);
      });
      data = Array.from(data);
    } else {
      data = Array.from(LittleFS.UintToBuffer(buffer, size));
    }

    for (let i = 0; i < size; i++) {
        crc = ((crc >>> 4) ^ rtable[(crc ^ (data[i] >>> 0)) & 0xf]) >>> 0;
        crc = ((crc >>> 4) ^ rtable[(crc ^ (data[i] >>> 4)) & 0xf]) >>> 0;
    }

    return crc;
  }

  allocDrop() {
    this.free.size = 0;
    this.free.i = 0;
    this.allocAck();
  }

  pairSwap(pair) {
    let t = pair[0];
    pair[0] = pair[1];
    pair[1] = t;
  }

  gstateHasorphans(a) {
    return !!this.tagSize(a.tag);
  }

  gstateGetorphans(a) {
    return this.tagSize(a.tag);
  }

  gstateHasmove(a) {
    return this.tagType1(a.tag);
  }

  gstateHasmovehere(a, pair) {
    return this.tagType1(a.tag) && this.pairCmp(a.pair, pair) == 0;
  }

  pairCmp(pairA, pairB) {
    return !(pairA[0] == pairB[0] || pairA[1] == pairB[1] ||
             pairA[0] == pairB[1] || pairA[1] == pairB[0]);
  }

  static bufferToUint(buffer, size) {
    const view = new DataView(buffer.buffer)
    let ret = [];
    let offset = 0;
    // If size > 4, we will return an array of Uints
    while(size > 0) {
      if (size >= 4) {
        ret.push(view.getUint32(offset, true));
        size -= 4;
        offset += 4;
      } else if (size >= 2) {
        ret.push(view.getUint16(offset, true));
        size -= 2;
        offset += 2;
      } else if (size >= 1) {
        ret.push(view.getUint8(offset, true));
        size -= 1;
        offset += 1;
      }
    }

    if (ret.length == 1) {
      return ret[0];
    }
    return ret;
  }

  static UintToBuffer(data, size) {
    let buffer = new Uint8Array(size);
    const view = new DataView(buffer.buffer);
    let offset = 0;

    while(size > 0) {
      if (size >= 4) {
        view.setUint32(offset, data, true);
        size -= 4;
        offset += 4;
      } else if (size >= 2) {
        view.setUint16(offset, data, true);
        size -= 2;
        offset += 2;
      } else if (size >= 1) {
        view.setUint8(offset, data, true);
        size -= 1;
        offset += 1;
      }
    }
    return buffer;
  }
  // Block Device Read
  bdRead(pcache, rcache, hint, block, off, bufferByRef, size, returnRaw=false) {
    let data = new Uint8Array(size);
    let dataPtr = 0;
    if (block >= this.cfg.blockCount ||
            off+size > this.cfg.blockSize) {
        return LFS_ERR_CORRUPT;
    }

    let bufferSize = size;

    while (size > 0) {
        let diff = size;

        if (pcache && block == pcache.block &&
                off < pcache.off + pcache.size) {
            if (off >= pcache.off) {
                // is already in pcache?
                diff = Math.min(diff, pcache.size - (off-pcache.off));
                //memcpy(data, pcache.buffer[off-pcache.off], diff);
                data.set(pcache.buffer.slice(off-pcache.off, off-pcache.off + diff), dataPtr);
                dataPtr += diff;
                off += diff;
                size -= diff;
                continue;
            }

            // pcache takes priority
            diff = Math.min(diff, pcache.off-off);
        }

        if (block == rcache.block &&
                off < rcache.off + rcache.size) {
            if (off >= rcache.off) {
                // is already in rcache?
                diff = Math.min(diff, rcache.size - (off-rcache.off));
                //memcpy(data, rcache.buffer[off-rcache.off], diff);
                data.set(rcache.buffer.slice(off-rcache.off, off-rcache.off + diff), dataPtr);

                dataPtr += diff;
                off += diff;
                size -= diff;
                continue;
            }

            // rcache takes priority
            diff = Math.min(diff, rcache.off-off);
        }

        if (size >= hint && off % this.cfg.readSize == 0 &&
                size >= this.cfg.readSize) {
            // bypass cache?
            diff = this.aligndown(diff, this.cfg.readSize);
            let err = this.cfg.read(block, off, data, diff);
            if (err) {
                return err;
            }

            dataPtr += diff;
            off += diff;
            size -= diff;
            continue;
        }

        // load to cache, first condition can no longer fail
        console.assert(block < this.cfg.blockCount);
        rcache.block = block;
        rcache.off = this.aligndown(off, this.cfg.readSize);
        rcache.size = Math.min(
                Math.min(
                    this.alignup(off+hint, this.cfg.readSize),
                    this.cfg.blockSize)
                - rcache.off,
                this.cfg.cacheSize);
        let err = this.cfg.read(rcache.block, rcache.off, rcache.buffer, rcache.size);

        console.assert(err <= 0);
        if (err) {
            return err;
        }
    }
    bufferByRef.set(data);
    if (!returnRaw) {
      bufferByRef.set(LittleFS.bufferToUint(bufferByRef.get(), bufferSize));
    }
    return 0;

  }

  bdFlush(pcache, rcache, validate) {
    if (pcache.block != LFS_BLOCK_NULL && pcache.block != LFS_BLOCK_INLINE) {
      console.assert(pcache.block < this.cfg.blockCount);
      let diff = this.alignup(pcache.size, this.cfg.progSize);
      let err = this.cfg.prog(pcache.block, pcache.off, pcache.buffer, diff);
      console.assert(err <= 0);
      if (err) {
          return err;
      }

      if (validate) {
          // check data on disk
          this.cacheDrop(rcache);
          let res = this.bdCmp(null, rcache, diff,
                  pcache.block, pcache.off, pcache.buffer, diff);
          if (res < 0) {
              return res;
          }

          if (res != LFS_CMP_EQ) {
              return LFS_ERR_CORRUPT;
          }
      }

      this.cacheZero(pcache);
    }

    return 0;
  }

  bdCmp(pcache, rcache, hint, block, off, buffer, size) {
    let data;
    if (typeof buffer === 'string') {
      data = toByteArray(buffer);
    } else {
      data = buffer;
    }

    let diff = 0;

    for (let i = 0; i < size; i += diff) {
        let bufferByRef = new ByRef();

        diff = Math.min(size-i, struct.calcsize("BBBBBBBB"));
        let res = this.bdRead(pcache, rcache, hint-i,
                block, off+i, bufferByRef, diff, true);
        let dat = bufferByRef.get();
        if (res) {
            return res;
        }

        res = this.memcmp(dat, data.slice(i), diff);

        if (res) {
            return res < 0 ? LFS_CMP_LT : LFS_CMP_GT;
        }
    }

    return LFS_CMP_EQ;
  }

  memcmp(array1, array2, size) {
    size = Math.min(array1.length, array2.length, size);
    for (let i = 0; i < size; i++) {
      if (array1[i] === array2[i]) {
        continue;
      } else if (array1[i] < array2[i]) {
        return -1;
      } else {
        return 1;
      }
    }

    return 0;
  }

  bdErase(block) {
    console.assert(block < this.cfg.blockCount);
    let err = this.cfg.erase(block);
    console.assert(err <= 0);
    return err;
  }

  bdProg(pcache, rcache, validate, block, off, buffer, size) {
    let data;
    let dataPtr = 0;
    if (buffer == null) {
      data = new Uint8Array(size);
    } else if (Array.isArray(buffer)) {
      data = new Uint8Array(size);
      const dataSize = parseInt(size / buffer.length);
      for(let [index, item] of buffer.entries()) {
        data.set(LittleFS.UintToBuffer(item, dataSize), index * dataSize);
      }
    } else if (typeof buffer === 'object') {
      data = new Uint8Array(size);
      const dataSize = parseInt(size / Object.entries(buffer).length);
      Object.values(buffer).forEach((value, index) => {
        data.set(LittleFS.UintToBuffer(value, dataSize), index * dataSize);
      });
    } else if (typeof buffer === 'string') {
      data = new Uint8Array(size);
      data.set(toByteArray(buffer));
    } else {
      data = LittleFS.UintToBuffer(buffer, size);
    }
    console.assert(block == LFS_BLOCK_INLINE || block < this.cfg.blockCount);
    console.assert(off + size <= this.cfg.blockSize);
    while (size > 0) {
        if (block == pcache.block &&
                off >= pcache.off &&
                off < pcache.off + this.cfg.cacheSize) {
            // already fits in pcache?
            let diff = Math.min(size, this.cfg.cacheSize - (off-pcache.off));
            //memcpy(&pcache->buffer[off-pcache->off], data, diff);
            pcache.buffer.set(data.slice(dataPtr, dataPtr + diff), off-pcache.off);

            dataPtr += diff;
            off += diff;
            size -= diff;

            pcache.size = Math.max(pcache.size, off - pcache.off);
            if (pcache.size == this.cfg.cacheSize) {
                // eagerly flush out pcache if we fill up
                let err = this.bdFlush(pcache, rcache, validate);
                if (err) {
                    return err;
                }
            }

            continue;
        }

        // pcache must have been flushed, either by programming an
        // entire block or manually flushing the pcache
        console.assert(pcache.block == LFS_BLOCK_NULL);

        // prepare pcache, first condition can no longer fail
        pcache.block = block;
        pcache.off = this.aligndown(off, this.cfg.progSize);
        pcache.size = 0;
    }

    return 0;
  }

  bdSync(pcache, rcache, validate) {
    this.cacheDrop(rcache);

    let err = this.bdFlush(pcache, rcache, validate);
    if (err) {
        return err;
    }

    err = this.cfg.sync();
    console.assert(err <= 0);
    return err;
  }

  mount() {
    // scan directory blocks for superblock and any global updates
    let dir = new MDir()
    dir.tail = [0, 1];
    let cycle = 0;
    let err;
    while (!this.pairIsnull(dir.tail)) {
        if (cycle >= this.cfg.blockCount/2) {
            // loop detected
            err = LFS_ERR_CORRUPT;
        }
        cycle += 1;

        // fetch next block in tail list
        let tag = this.dirFetchmatch(dir, dir.tail,
                this.mkTag(0x7ff, 0x3ff, 0),
                this.mkTag(LFS_TYPE_SUPERBLOCK, 0, 8),
                new ByRef(null),
                this.dirFindMatch.bind(this),
                new DirFindMatch({name: "littlefs", size: 8}));
        if (tag < 0) {
            err = tag;
        }


        // has superblock?
        if (tag && !this.tagIsdelete(tag)) {
            // update root
            this.root[0] = dir.pair[0];
            this.root[1] = dir.pair[1];

            // grab superblock
            let superBlockByRef = new ByRef(new Uint8Array(struct.calcsize("IIIIII")));
            tag = this.dirGet(dir, this.mkTag(0x7ff, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_INLINESTRUCT, 0, superBlockByRef.get().byteLength),
                    superBlockByRef);
            if (tag < 0) {
                err = tag;
            }
            let superblock = new SuperBlock();
            superblock.setFromBuffer(superBlockByRef.get());
            this.superblockFromle32(superblock);
            // check version
            let major_version = (0xffff & (superblock.version >> 16));
            let minor_version = (0xffff & (superblock.version >>  0));
            if ((major_version != LFS_DISK_VERSION_MAJOR ||
                 minor_version > LFS_DISK_VERSION_MINOR)) {
                console.warn("Invalid version v" + major_version + "." + minor_version);
                err = LFS_ERR_INVAL;
            }

            // check superblock configuration
            if (superblock.nameMax) {
                if (superblock.nameMax > this.nameMax) {
                    console.error("Unsupported nameMax (" + superblock.nameMax + " > " + this.nameMax + ")");
                    err = LFS_ERR_INVAL;
                }

                this.nameMax = superblock.nameMax;
            }

            if (superblock.fileMax) {
                if (superblock.fileMax > this.fileMax) {
                    console.error("Unsupported fileMax (" + superblock.fileMax + " > " + this.fileMax + ")");
                    err = LFS_ERR_INVAL;
                }

                this.fileMax = superblock.fileMax;
            }

            if (superblock.attrMax) {
                if (superblock.attrMax > this.attrMax) {
                    console.error("Unsupported attrMax (" + superblock.attrMax + " > " + this.attrMax + ")");
                    err = LFS_ERR_INVAL;
                }

                this.attrMax = superblock.attrMax;
            }
        }

        // has gstate?
        err = this.dirGetgstate(dir, this.gstate);
    }

    // found superblock?
    if (this.pairIsnull(this.root)) {
        err = LFS_ERR_INVAL;
    }

    // update littlefs with gstate
    if (!this.gstateIszero(this.gstate)) {
        console.warn("Found pending gstate " + toHex(this.gstate.tag, 8) + " " + toHex(this.gstate.pair[0], 8) + " " + toHex(this.gstate.pair[1], 8));
    }
    this.gstate.tag += !this.tagIsvalid(this.gstate.tag);
    this.gdisk = this.gstate;

    // setup free lookahead, to distribute allocations uniformly across
    // boots, we start the allocator at a random location
    this.free.off = this.seed % this.cfg.blockCount;
    this.allocDrop();

    return 0;

  }

  unmount() {
    return this.deinit();
  }

  deinit() {
    // Nothing to do here cause this is JavaScript
    return 0;
  }

  dirCommit(dir, attrs) {
    // check for any inline files that aren't RAM backed and
    // forcefully evict them, needed for filesystem consistency
    if (attrs === null) {
      attrs = [];
    }

    for (let f = this.mList; f; f = f.next) {
        if (dir != f.m && this.pairCmp(f.m.pair, dir.pair) == 0 &&
                f.type == LFS_TYPE_REG && (f.flags & LFS_F_INLINE) &&
                f.ctz.size > this.cfg.cacheSize) {
            let err = this.fileOutline(f);
            if (err) {
                return err;
            }

            err = this.fileFlush(f);
            if (err) {
                return err;
            }
        }
    }

    // calculate changes to the directory
    let olddir = dir;
    let hasdelete = false;
    for (let i = 0; i < attrs.length; i++) {
        if (this.tagType3(attrs[i].tag) == LFS_TYPE_CREATE) {
            dir.count += 1;
        } else if (this.tagType3(attrs[i].tag) == LFS_TYPE_DELETE) {
            console.assert(dir.count > 0);
            dir.count -= 1;
            hasdelete = true;
        } else if (this.tagType1(attrs[i].tag) == LFS_TYPE_TAIL) {
            dir.tail[0] = attrs[i].buffer[0];
            dir.tail[1] = attrs[i].buffer[1];
            dir.split = (this.tagChunk(attrs[i].tag) & 1);
            this.pairFromle32(dir.tail);
        }
    }

    // should we actually drop the directory block?
    if (hasdelete && dir.count == 0) {
        let pdir;
        let err = this.fsPred(lfs, dir.pair, pdir);
        if (err && err != LFS_ERR_NOENT) {
            this.copyObjProps(dir, olddir);
            return err;
        }

        if (err != LFS_ERR_NOENT && pdir.split) {
            err = this.dirDrop(pdir, dir);
            if (err) {
                this.copyObjProps(dir, olddir);
                return err;
            }
        }
    }

  let doCompact = false;
  attempt_commit:  if (dir.erased || dir.count >= 0xff) {
        // try to commit
        let commit = new Commit({
            block: dir.pair[0],
            off: dir.off,
            ptag: dir.etag,
            crc: 0xffffffff,

            begin: dir.off,
            end: (this.cfg.metadataMax ?
                this.cfg.metadataMax : this.cfg.blockSize) - 8,
        });

        // traverse attrs that need to be written out
        this.pairTole32(dir.tail);
        let err = this.dirTraverse(dir, dir.off, dir.etag, attrs, attrs.length,
                0, 0, 0, 0, 0, this.dirCommitCommit.bind(this), commit);
        this.pairFromle32(dir.tail);
        if (err) {
            if (err == LFS_ERR_NOSPC || err == LFS_ERR_CORRUPT) {
              doCompact = true;
              break attempt_commit;
            }
            this.copyObjProps(dir, olddir);
            return err;
        }

        // commit any global diffs if we have any
        let delta = new GState({tag: 0});
        this.gstateXor(delta, this.gstate);
        this.gstateXor(delta, this.gdisk);
        this.gstateXor(delta, this.gdelta);
        delta.tag &= ~this.mkTag(0, 0, 0x3ff);
        if (!this.gstateIszero(delta)) {
            let err = this.dirGetgstate(dir, delta);
            if (err) {
                this.copyObjProps(dir, olddir);
                return err;
            }

            this.gstateTole32(delta);
            err = this.dirCommitattr(
              commit,
              this.mkTag(LFS_TYPE_MOVESTATE, 0x3ff, struct.calcsize("I")),
              delta
            );
            if (err) {
                if (err == LFS_ERR_NOSPC || err == LFS_ERR_CORRUPT) {
                    doCompact = true;
                    break attempt_commit;
                }
                this.copyObjProps(dir, olddir);
                return err;
            }
        }

        // finalize commit with the crc
        err = this.dirCommitcrc(commit);
        if (err) {
            if (err == LFS_ERR_NOSPC || err == LFS_ERR_CORRUPT) {
                doCompact = true;
                break attempt_commit;

            }
            this.copyObjProps(dir, olddir);
            return err;
        }

        // successful commit, update dir
        console.assert(commit.off % this.cfg.progSize == 0);
        dir.off = commit.off;
        dir.etag = commit.ptag;
        // and update gstate
        this.gdisk = this.gstate;
        this.gdelta = new GState({tag: 0});
    } else {
      doCompact = true;
      break attempt_commit;
    }

    if (doCompact) {
        // fall back to compaction
        this.cacheDrop(this.pcache);

        let err = this.dirCompact(dir, attrs, attrs.length, dir, 0, dir.count);
        if (err) {
            this.copyObjProps(dir, olddir);
        }
    }
    // this complicated bit of logic is for fixing up any active
    // metadata-pairs that we may have affected
    //
    // note we have to make two passes since the mdir passed to
    // lfs_dir_commit could also be in this list, and even then
    // we need to copy the pair so they don't get clobbered if we refetch
    // our mdir.
    for (let d = this.mList; d; d = d.next) {
        if (d.m != dir && this.pairCmp(d.m.pair, olddir.pair) == 0) {
            d.m = dir;
            for (let i = 0; i < attrs.length; i++) {
                if (this.tagType3(attrs[i].tag) == LFS_TYPE_DELETE &&
                        d.id == this.tagId(attrs[i].tag)) {
                    d.m.pair[0] = LFS_BLOCK_NULL;
                    d.m.pair[1] = LFS_BLOCK_NULL;
                } else if (this.tagType3(attrs[i].tag) == LFS_TYPE_DELETE &&
                        d.id > this.tagId(attrs[i].tag)) {
                    d.id -= 1;
                    if (d.type == LFS_TYPE_DIR) {
                        d.pos -= 1;
                    }
                } else if (this.tagType3(attrs[i].tag) == LFS_TYPE_CREATE &&
                        d.id >= this.tagId(attrs[i].tag)) {
                    d.id += 1;
                    if (d.type == LFS_TYPE_DIR) {
                        d.pos += 1;
                    }
                }
            }
        }
    }

    for (let d = this.mList; d; d = d.next) {
        if (this.pairCmp(d.m.pair, olddir.pair) == 0) {
            while (d.id >= d.m.count && d.m.split) {
                // we split and id is on tail now
                d.id -= d.m.count;
                let err = this.dirFetch(d.m, d.m.tail);
                if (err) {
                    return err;
                }
            }
        }
    }

    return 0;
  }

  dirCompact(dir, attrs, attrcount, source, begin, end) {
    // save some state in case block is bad
    const oldpair = [dir.pair[0], dir.pair[1]];
    let relocated = false;
    let tired = false;
    let doRelocate = false;
    // should we split?
    while (end - begin > 1) {
        // find size
        let size = 0;
        let sizeObj = {size: size}
        let err = this.dirTraverse(source, 0, 0xffffffff, attrs, attrcount,
                this.mkTag(0x400, 0x3ff, 0),
                this.mkTag(LFS_TYPE_NAME, 0, 0),
                begin, end, -begin,
                this.dirCommitSize.bind(this), sizeObj);
        size = sizeObj.size;
        if (err) {
            return err;
        }

        // space is complicated, we need room for tail, crc, gstate,
        // cleanup delete, and we cap at half a block to give room
        // for metadata updates.
        if (end - begin < 0xff &&
                size <= Math.min(this.cfg.blockSize - 36,
                    this.alignup((this.cfg.metadataMax ?
                            this.cfg.metadataMax : this.cfg.blockSize)/2,
                        this.cfg.progSize))) {
            break;
        }

        // can't fit, need to split, we should really be finding the
        // largest size that fits with a small binary search, but right now
        // it's not worth the code size
        let split = (end - begin) / 2;
        err = this.dirSplit(dir, attrs, attrcount, source, begin+split, end);
        if (err) {
            // if we fail to split, we may be able to overcompact, unless
            // we're too big for even the full block, in which case our
            // only option is to error
            if (err == LFS_ERR_NOSPC && size <= this.cfg.blockSize - 36) {
                break;
            }
            return err;
        }

        end = begin + split;
    }

    // increment revision count
    dir.rev += 1;
    // If our revision count == n * block_cycles, we should force a relocation,
    // this is how littlefs wear-levels at the metadata-pair level. Note that we
    // actually use (block_cycles+1)|1, this is to avoid two corner cases:
    // 1. block_cycles = 1, which would prevent relocations from terminating
    // 2. block_cycles = 2n, which, due to aliasing, would only ever relocate
    //    one metadata block in the pair, effectively making this useless
    if (this.cfg.blockCycles > 0 && (dir.rev % ((this.cfg.blockCycles+1)|1) == 0)) {
        if (this.pairCmp(dir.pair, [0, 1]) == 0) {
            // oh no! we're writing too much to the superblock,
            // should we expand?
            let res = this.fsRawsize();
            if (res < 0) {
                return res;
            }

            // do we have extra space? littlefs can't reclaim this space
            // by itself, so expand cautiously
            if (res < this.cfg.blockCount/2) {
                console.warn("Expanding superblock at rev " + dir.rev);
                let err = this.dirSplit(dir, attrs, attrcount, source, begin, end);
                if (err && err != LFS_ERR_NOSPC) {
                    return err;
                }

                // welp, we tried, if we ran out of space there's not much
                // we can do, we'll error later if we've become frozen
                if (!err) {
                    end = begin;
                }
            }
        } else {
            // we're writing too much, time to relocate
            tired = true;
            doRelocate = true;
        }
    }
    // begin loop to commit compaction to blocks until a compact sticks
main_while_loop: while (true) {
compaction_block:  if (!doRelocate) {
            // setup commit state
            let commit = new Commit ({
                block: dir.pair[1],
                off: 0,
                ptag: 0xffffffff,
                crc: 0xffffffff,

                begin: 0,
                end: (this.cfg.metadataMax ?
                    this.cfg.metadataMax : this.cfg.blockSize) - 8,
            });

            // erase block to write to
            let err = this.bdErase(dir.pair[1]);
            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                  break compaction_block;
                }
                return err;
            }

            // write out header
            dir.rev = this.tole32(dir.rev);
            err = this.dirCommitprog(commit, dir.rev, struct.calcsize("I"));
            dir.rev = this.fromle32(dir.rev);
            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                  break compaction_block;
                }
                return err;
            }

            // traverse the directory, this time writing out all unique tags
            err = this.dirTraverse(source, 0, 0xffffffff, attrs, attrcount,
                    this.mkTag(0x400, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_NAME, 0, 0),
                    begin, end, -begin,
                    this.dirCommitCommit.bind(this), commit);
            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                  break compaction_block;
                }
                return err;
            }

            // commit tail, which may be new after last size check
            if (!this.pairIsnull(dir.tail)) {
                this.pairTole32(dir.tail);
                err = this.dirCommitattr(commit,
                        this.mkTag(LFS_TYPE_TAIL + dir.split, 0x3ff, 8),
                        dir.tail);
                this.pairFromle32(dir.tail);
                if (err) {
                    if (err == LFS_ERR_CORRUPT) {
                      break compaction_block;
                    }
                    return err;
                }
            }

            // bring over gstate?
            let delta = new GState({tag: 0});
            if (!relocated) {
                this.gstateXor(delta, this.gdisk);
                this.gstateXor(delta, this.gstate);
            }
            this.gstateXor(delta, this.gdelta);
            delta.tag &= ~this.mkTag(0, 0, 0x3ff);

            err = this.dirGetgstate(dir, delta);
            if (err) {
                return err;
            }

            if (!this.gstateIszero(delta)) {
                this.gstateTole32(delta);
                err = this.dirCommitattr(commit,
                        this.mkTag(LFS_TYPE_MOVESTATE, 0x3ff,
                            struct.calcsize("III")), delta);
                if (err) {
                    if (err == LFS_ERR_CORRUPT) {
                      break compaction_block;
                    }
                    return err;
                }
            }

            // complete commit with crc
            err = this.dirCommitcrc(commit);
            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                  break compaction_block;
                }
                return err;
            }

            // successful compaction, swap dir pair to indicate most recent
            console.assert(commit.off % this.cfg.progSize == 0);
            this.pairSwap(dir.pair);
            dir.count = end - begin;
            dir.off = commit.off;
            dir.etag = commit.ptag;
            // update gstate
            this.gdelta = new GState({tag: 0});
            if (!relocated) {
                this.gdisk = this.gstate;
            }
            break main_while_loop;
        } // end compaction_block

// relocate:
        // commit was corrupted, drop caches and prepare to relocate block
        relocated = true;
        this.cacheDrop(this.pcache);
        if (!tired) {
            // Block is detected as unusable in normal Flash
            console.warn("Bad block at " + toHex(dir.pair[1], 8));
        }

        // can't relocate superblock, filesystem is now frozen
        if (this.pairCmp(dir.pair, [0, 1]) == 0) {
            console.warn("Superblock " + toHex(dir.pair[1], 8) + " has become unwritable");
            return LFS_ERR_NOSPC;
        }

        // relocate half of pair
        let blockObj = new ByRef();
        let err = this.alloc(blockObj);
        dir.pair[1] = blockObj.get();
        if (err && (err != LFS_ERR_NOSPC || !tired)) {
            return err;
        }

        tired = false;
        continue;
    } // end main_while_loop

    if (relocated) {
        // update references if we relocated
        console.warn("Relocating {" + toHex(oldpair[0], 8) + ", " + toHex(oldpair[1], 8) + "} " +
                    "-> {" + toHex(dir.pair[0], 8) + ", " + toHex(dir.pair[1], 8) + "}");
        let err = this.fsRelocate(oldpair, dir.pair);
        if (err) {
            return err;
        }
    }

    return 0;
  }

  dirTraverse(dir, off, ptag, attrs, attrcount, tmask, ttag, begin, end, diff, callback, data) {
    // iterate over directory and attrs
    let attrPtr = 0;
    while (true) {
        let tag;
        let buffer;
        let disk = new Diskoff();
        if (off+this.tagDsize(ptag) < dir.off) {
            off += this.tagDsize(ptag);
            let bufferByRef = new ByRef();
            let err = this.bdRead(null, this.rcache, struct.calcsize("I"),
                    dir.pair[0], off, bufferByRef, struct.calcsize("I"));
            tag = bufferByRef.get();
            if (err) {
                return err;
            }

            tag = ((this.fromBe32(tag) ^ ptag) >>> 0) | 0x80000000;
            disk.block = dir.pair[0];
            disk.off = off + struct.calcsize("I");
            buffer = disk;
            ptag = tag;
        } else if (attrcount > 0) {
            tag = attrs[attrPtr].tag;
            buffer = attrs[attrPtr].buffer;
            attrPtr += 1;
            attrcount -= 1;
        } else {
            return 0;
        }

        let mask = this.mkTag(0x7ff, 0, 0);
        if ((mask & tmask & tag) != (mask & tmask & ttag)) {
            continue;
        }

        // do we need to filter? inlining the filtering logic here allows
        // for some minor optimizations
        if (this.tagId(tmask) != 0) {
            // scan for duplicates and update tag based on creates/deletes
            let filter = this.dirTraverse(dir, off, ptag, attrs, attrcount,
                    0, 0, 0, 0, 0, this.dirTraverseFilter.bind(this), tag);
            if (filter < 0) {
                return filter;
            }

            if (filter) {
                continue;
            }

            // in filter range?
            if (!(this.tagId(tag) >= begin && this.tagId(tag) < end)) {
                continue;
            }
        }

        // handle special cases for mcu-side operations
        if (this.tagType3(tag) == LFS_FROM_NOOP) {
            // do nothing
        } else if (this.tagType3(tag) == LFS_FROM_MOVE) {
            let fromid = this.tagSize(tag);
            let toid = this.tagId(tag);
            let err = this.dirTraverse(buffer, 0, 0xffffffff, null, 0,
                    this.mkTag(0x600, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_STRUCT, 0, 0),
                    fromid, fromid+1, toid-fromid+diff,
                    callback, data);
            if (err) {
                return err;
            }
        } else if (this.tagType3(tag) == LFS_FROM_USERATTRS) {
            let a = buffer;
            for (let i = 0; i < this.tagSize(tag); i++) {
                let err = callback(data, this.mkTag(LFS_TYPE_USERATTR + a[i].type,
                        this.tagId(tag) + diff, a[i].size), a[i].buffer);
                if (err) {
                    return err;
                }
            }
        } else {
            let err = callback(data, tag + this.mkTag(0, diff, 0), buffer);
            if (err) {
                return err;
            }
        }
    }
}

  dirTraverseFilter(p, tag, buffer) {
    let filtertag = p;
    // which mask depends on unique bit in tag structure
    let mask = (tag & this.mkTag(0x100, 0, 0))
            ? this.mkTag(0x7ff, 0x3ff, 0)
            : this.mkTag(0x700, 0x3ff, 0);

    // check for redundancy
    if ((mask & tag) == (mask & filtertag) ||
            this.tagIsdelete(filtertag) ||
            (this.mkTag(0x7ff, 0x3ff, 0) & tag) == (
                this.mkTag(LFS_TYPE_DELETE, 0, 0) |
                    (this.mkTag(0, 0x3ff, 0) & filtertag))) {
        return true;
    }

    // check if we need to adjust for created/deleted tags
    if (this.tagType1(tag) == LFS_TYPE_SPLICE &&
            this.tagId(tag) <= this.tagId(filtertag)) {
        filtertag += this.mkTag(0, this.tagSplice(tag), 0); // Likely ref error
    }

    return false;
  }

  dirSplit() {
    console.warn("dirSplit not implemented");
  }

  dirFind(dir, pathByRef, idByRef) {
    // we reduce path to a single name if we can find it
    if (idByRef.get()) {
        idByRef.set(0x3ff);
    }
    let name = 0;
    let path = pathByRef.get();
    // default to root dir
    let tag = this.mkTag(LFS_TYPE_DIR, 0x3ff, 0);
    dir.tail[0] = this.root[0];
    dir.tail[1] = this.root[1];
    while (true) {
        // skip slashes
        name += path.indexOf("/") + 1;
        let namelen = path.slice(name).indexOf("/");
        if (namelen == -1) {
          namelen = path.slice(name).length;
        }
        // skip '.' and root '..'
        if ((namelen == 1 && path.substr(name, 1) == ".") ||
            (namelen == 2 && path.substr(name, 2) == "..")) {
            name += namelen;
            continue;
        }

        // skip if matched by '..' in name
        let suffix = path.substr(name + namelen)
        let sufflen;
        let depth = 1;
        while (true) {
            suffix += path.indexOf("/") + 1;
            sufflen = path.slice(suffix).indexOf("/");
            if (sufflen <= 0) {
                break;
            }

            if (sufflen == 2 && path.substr(suffix, 2) == "..") {
                depth -= 1;
                if (depth == 0) {
                    name = suffix + sufflen;
                    continue;
                }
            } else {
                depth += 1;
            }

            suffix += sufflen;
        }

        // found path
        if (name == path.length) {
            return tag;
        }

        // update what we've found so far
        path = path.slice(name);
        pathByRef.set(path);
        name = 0;

        // only continue if we hit a directory
        if (this.tagType3(tag) != LFS_TYPE_DIR) {
            return LFS_ERR_NOTDIR;
        }

        // grab the entry data
        if (this.tagId(tag) != 0x3ff) {
            let res = this.dirGet(dir, this.mkTag(0x700, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_STRUCT, this.tagId(tag), 8), dir.tail);
            if (res < 0) {
                return res;
            }
            this.pairFromle32(dir.tail);
        }

        // find entry matching name
        while (true) {
            tag = this.dirFetchmatch(dir, dir.tail,
                    this.mkTag(0x780, 0, 0),
                    this.mkTag(LFS_TYPE_NAME, 0, namelen),
                     // are we last name?
                    path.slice(name).indexOf('/') < 0 ? idByRef : new ByRef(null),
                    this.dirFindMatch.bind(this),
                    new DirFindMatch({name: path.slice(name), size: namelen})
                  );
            if (tag < 0) {
                return tag;
            }

            if (tag) {
                break;
            }

            if (!dir.split) {
                return LFS_ERR_NOENT;
            }
        }

        // to next name
        name += namelen;
    }
  }

  dirCommitCommit(p, tag, buffer) {
    return this.dirCommitattr(p, tag, buffer);
  }

  dirCommitcrc(commit) {
    // align to program units
    const end = this.alignup(commit.off + 2 * struct.calcsize("I"), this.cfg.progSize);
    let off1 = 0;
    let crc1 = 0;

    // create crc tags to fill up remainder of commit, note that
    // padding is not crc'd, which lets fetches skip padding but
    // makes committing a bit more complicated
    while (commit.off < end) {
        let off = commit.off + struct.calcsize("I");
        let noff = Math.min(end - off, 0x3fe) + off;
        if (noff < end) {
            noff = Math.min(noff, end - struct.calcsize("II"));
        }

        // read erased state from next program unit
        let tag = 0xffffffff;
        let bufferByRef = new ByRef();
        let err = this.bdRead(null, this.rcache, struct.calcsize("I"),
                commit.block, noff, bufferByRef, struct.calcsize("I"));
        if (err && err != LFS_ERR_CORRUPT) {
            return err;
        }
        tag = bufferByRef.get();

        // build crc tag
        let reset = !!(~this.fromBe32(tag) >>> 31) ? 1 : 0;
        tag = this.mkTag(LFS_TYPE_CRC + reset, 0x3ff, noff - off);

        // write out crc
        let footer = new Array(2);
        footer[0] = this.toBe32((tag ^ commit.ptag) >>> 0);
        commit.crc = this.crc(commit.crc, footer[0], struct.calcsize("I"));
        footer[1] = this.tole32(commit.crc);
        err = this.bdProg(this.pcache, this.rcache, false, commit.block, commit.off, footer, struct.calcsize("II"));
        if (err) {
            return err;
        }

        // keep track of non-padding checksum to verify
        if (off1 == 0) {
            off1 = commit.off + struct.calcsize("I");
            crc1 = commit.crc;
        }

        commit.off += struct.calcsize("I") + this.tagSize(tag);
        commit.ptag = (tag ^ (reset << 31)) >>> 0;
        commit.crc = 0xffffffff; // reset crc for next "commit"
    }

    // write buffers to flash and flush
    let err = this.bdSync(this.pcache, this.rcache, false);
    if (err) {
        return err;
    }

    // successful commit, check checksums to make sure
    let off = commit.begin;
    let noff = off1;
    while (off < end) {
        let crc = 0xffffffff;
        for (let i = off; i < noff + struct.calcsize("I"); i++) {
            // check against written crc, may catch blocks that
            // become readonly and match our commit size exactly
            if (i == off1 && crc != crc1) {
                return LFS_ERR_CORRUPT;
            }

            // leave it up to caching to make this efficient
            let bufferByRef = new ByRef();

            err = this.bdRead(null, this.rcache, noff + struct.calcsize("I") - i,
                    commit.block, i, bufferByRef, 1);
            if (err) {
                return err;
            }
            let dat = bufferByRef.get();
            crc = this.crc(crc, dat, 1);
        }

        // detected write error?
        if (crc != 0) {
            return LFS_ERR_CORRUPT;
        }

        // skip padding
        off = Math.min(end - noff, 0x3fe) + noff;
        if (off < end) {
            off = Math.min(off, end - 2 * struct.calcsize("I"));
        }
        noff = off + struct.calcsize("I");
    }

    return 0;
  }

  fsRawsize() {
    console.warn("fsRawsize not implemented");
  }

  dirCommitSize() {
    console.warn("dirCommitSize not implemented");
  }

  dirCommitattr(commit, tag, buffer) {
    // check if we fit
    let dsize = this.tagDsize(tag);
    if (commit.off + dsize > commit.end) {
        return LFS_ERR_NOSPC;
    }
    // write out tag
    let ntag = this.toBe32(((tag & 0x7fffffff) ^ commit.ptag) >>> 0);
    let err = this.dirCommitprog(commit, ntag, struct.calcsize("I")); // ntag by ref
    if (err) {
        return err;
    }

    if (!(tag & 0x80000000)) {
        // from memory
        err = this.dirCommitprog(commit, buffer, dsize - struct.calcsize("I"));
        if (err) {
            return err;
        }
    } else {
        // from disk
        let disk = buffer;
        for (let i = 0; i < dsize-struct.calcsize("I"); i++) {
            // rely on caching to make this efficient
            let bufferByRef = new ByRef();
            err = this.bdRead(null, this.rcache, dsize-struct.calcsize("I")-i,
                    disk.block, disk.off+i, bufferByRef, 1);
            let dat = bufferByRef.get();
            if (err) {
                return err;
            }

            err = this.dirCommitprog(commit, dat, 1);
            if (err) {
                return err;
            }
        }
    }

    commit.ptag = tag & 0x7fffffff;
    return 0;
  }

  dirDrop() {
    console.warn("dirDrop not implemented");
  }

  dirGetread() {
    console.warn("dirGetread not implemented");
  }

  dirGet(dir, gmask, gtag, buffer) {
    return this.dirGetslice(dir, gmask, gtag, 0, buffer, this.tagSize(gtag));
  }

  dirGetslice(dir, gmask, gtag, goff, gbuffer, gsize) {
    let off = dir.off;
    let ntag = dir.etag;
    let gdiff = 0;

    if (this.gstateHasmovehere(this.gdisk, dir.pair) &&
            this.tagId(gmask) != 0 &&
            this.tagId(this.gdisk.tag) <= this.tagId(gtag)) {
        // synthetic moves
        gdiff -= this.mkTag(0, 1, 0);
    }

    // iterate over dir block backwards (for faster lookups)
    while (off >= struct.calcsize("I") + this.tagDsize(ntag)) {
        off -= this.tagDsize(ntag);
        let tag = ntag;
        let bufferByRef = new ByRef();
        let err = this.bdRead(null, this.rcache, struct.calcsize("I"),
                dir.pair[0], off, bufferByRef, struct.calcsize("I"));
        if (err) {
            return err;
        }
        ntag = bufferByRef.get();
        ntag = (this.fromBe32(ntag) ^ tag) & 0x7fffffff;

        if (this.tagId(gmask) != 0 &&
                this.tagType1(tag) == LFS_TYPE_SPLICE &&
                this.tagId(tag) <= this.tagId(gtag - gdiff)) {
            if (tag == (this.mkTag(LFS_TYPE_CREATE, 0, 0) |
                    (this.mkTag(0, 0x3ff, 0) & (gtag - gdiff)))) {
                // found where we were created
                return LFS_ERR_NOENT;
            }

            // move around splices
            gdiff += this.mkTag(0, this.tagSplice(tag), 0);
        }

        if ((gmask & tag) == (gmask & (gtag - gdiff))) {
            if (this.tagIsdelete(tag)) {
                return LFS_ERR_NOENT;
            }

            let diff = Math.min(this.tagSize(tag), gsize);
            let bufferByRef = new ByRef();
            err = this.bdRead(null, this.rcache, diff,
                    dir.pair[0], off + struct.calcsize("I") + goff, bufferByRef, diff, true);
            if (err) {
                return err;
            }

            gbuffer.data.set(bufferByRef.get());
            //memset((uint8_t*)gbuffer + diff, 0, gsize - diff);
            gbuffer.data.set(new Uint8Array(gsize-diff).fill(0), diff)

            return tag + gdiff;
        }
    }

    return LFS_ERR_NOENT;
  }

  dirGetgstate(dir, gstate) {
    let temp = new GState();
    let res = this.dirGet(dir, this.mkTag(0x7ff, 0, 0),
            this.mkTag(LFS_TYPE_MOVESTATE, 0, struct.calcsize("III")), temp);
    if (res < 0 && res != LFS_ERR_NOENT) {
        return res;
    }

    if (res != LFS_ERR_NOENT) {
        // xor together to find resulting gstate
        this.gstateFromle32(temp);
        this.gstateXor(gstate, temp);
    }

    return 0;
  }

  cacheDrop(cache) {
    cache.block = LFS_BLOCK_NULL;
  }

  cacheZero(cache) {
    cache.buffer.fill(0xFF);
    cache.block = LFS_BLOCK_NULL;
  }

  fsPred() {
    console.warn("fsPred not implemented");
  }

  fsRelocate() {
    console.warn("fsRelocate not implemented");
  }

  gstateXor(gstateA, gstateB) {
    gstateA.tag ^= gstateB.tag
    gstateA.pair[0] ^= gstateB.pair[0]
    gstateA.pair[1] ^= gstateB.pair[1]
  }

  gstateIszero(gstate) {
    return gstate.tag === 0 && gstate.pair[0] === 0 && gstate.pair[1] === 0;
  }

  gstateTole32(gstate) {
    gstate.tag     = this.tole32(gstate.tag);
    gstate.pair[0] = this.tole32(gstate.pair[0]);
    gstate.pair[1] = this.tole32(gstate.pair[1]);
  }

  gstateFromle32(gstate) {
    gstate.tag     = this.fromle32(gstate.tag);
    gstate.pair[0] = this.fromle32(gstate.pair[0]);
    gstate.pair[1] = this.fromle32(gstate.pair[1]);
  }

  scmp(a, b) {
    return parseInt(a - b);
  }

  tole32(value) {
    return this.fromle32(value);
  }

  fromle32(value) {
    const data = Array.from(LittleFS.UintToBuffer(value, 4));
    value = (data[0] <<  0) |
            (data[1] <<  8) |
            (data[2] << 16) |
            (data[3] << 24);
    return value >>> 0;
  }

  toBe32(value) {
    return this.fromBe32(value);
  }

  fromBe32(value) {
    const data = Array.from(LittleFS.UintToBuffer(value, 4));
    value = (data[0] << 24) |
            (data[1] << 16) |
            (data[2] <<  8) |
            (data[3] <<  0);
    return value >>> 0;
  }

  ctzFromle32(ctz) {
    ctz.head = this.fromle32(ctz.head);
    ctz.size = this.fromle32(ctz.size);
  }

  ctzTole32(ctz) {
    ctz.head = this.tole32(ctz.head);
    ctz.size = this.tole32(ctz.size);
  }

  pairFromle32(pair) {
    pair[0] = this.fromle32(pair[0]);
    pair[1] = this.fromle32(pair[1]);
  }

  pairTole32(pair) {
    pair[0] = this.tole32(pair[0]);
    pair[1] = this.tole32(pair[1]);
  }

  superblockTole32(superblock) {
    superblock.version    = this.tole32(superblock.version);
    superblock.blockSize  = this.tole32(superblock.blockSize);
    superblock.blockCount = this.tole32(superblock.blockCount);
    superblock.nameMax    = this.tole32(superblock.nameMax);
    superblock.fileMax    = this.tole32(superblock.fileMax);
    superblock.attrMax    = this.tole32(superblock.attrMax);
  }

  superblockFromle32(superblock) {
    superblock.version    = this.fromle32(superblock.version);
    superblock.blockSize  = this.fromle32(superblock.blockSize);
    superblock.blockCount = this.fromle32(superblock.blockCount);
    superblock.nameMax    = this.fromle32(superblock.nameMax);
    superblock.fileMax    = this.fromle32(superblock.fileMax);
    superblock.attrMax    = this.fromle32(superblock.attrMax);
  }

  fileOpen(file, path, flags) {
    let defaults = new FileConfig({attrCount: 0});
    let err = this.fileOpencfg(file, path, flags, defaults);
    return err;
  }

  fileOpencfg(file, path, flags, cfg) {
      let err;

  main_block: if (true) {
    // deorphan if we haven't yet, needed at most once after poweron
    if ((flags & LFS_O_WRONLY) == LFS_O_WRONLY) {
        let err = this.fsForceconsistency();
        if (err) {
            return err;
        }
    }
    // setup simple file details
    file.cfg = cfg;
    file.flags = flags;
    file.pos = 0;
    file.off = 0;
    file.cache.buffer = null;

    // allocate entry for file if it doesn't exist
    let pathByRef = new ByRef(path);
    let idByRef = new ByRef(file.id);
    let tag = this.dirFind(file.m, pathByRef, idByRef);
    file.id = idByRef.get();
    path = pathByRef.get();
    if (tag < 0 && !(tag == LFS_ERR_NOENT && file.id != 0x3ff)) {
        err = tag;
        break main_block;
    }

    // get id, add to list of mdirs to catch update changes
    file.type = LFS_TYPE_REG;
    this.mlistAppend(file);

    if (tag == LFS_ERR_NOENT) {
        if (!(flags & LFS_O_CREAT)) {
            err = LFS_ERR_NOENT;
            break main_block;
        }

        // check that name fits
        let nlen = path.length;
        if (nlen > this.nameMax) {
            err = LFS_ERR_NAMETOOLONG;
            break main_block;
        }

        // get next slot and create entry to remember name
        err = this.dirCommit(file.m, this.mkAttrs(
                [this.mkTag(LFS_TYPE_CREATE, file.id, 0), null],
                [this.mkTag(LFS_TYPE_REG, file.id, nlen), path],
                [this.mkTag(LFS_TYPE_INLINESTRUCT, file.id, 0), null]
              ));
        if (err) {
            err = LFS_ERR_NAMETOOLONG;
            break main_block;
        }

        tag = this.mkTag(LFS_TYPE_INLINESTRUCT, 0, 0);
    } else if (flags & LFS_O_EXCL) {
        err = LFS_ERR_EXIST;
        break main_block;
    } else if (this.tagType3(tag) != LFS_TYPE_REG) {
        err = LFS_ERR_ISDIR;
        break main_block;
    } else if (flags & LFS_O_TRUNC) {
        // truncate if requested
        tag = this.mkTag(LFS_TYPE_INLINESTRUCT, file.id, 0);
        file.flags |= LFS_F_DIRTY;
    } else {
        // try to load what's on disk, if it's inlined we'll fix it later
        tag = this.dirGet(file.m, this.mkTag(0x700, 0x3ff, 0),
                this.mkTag(LFS_TYPE_STRUCT, file.id, 8), file.ctz);
        if (tag < 0) {
            err = tag;
            break main_block;
        }
        this.ctzFromle32(file.ctz);
    }

    // fetch attrs
    for (let i = 0; i < file.cfg.attr_count; i++) {
        // if opened for read / read-write operations
        if ((file.flags & LFS_O_RDONLY) == LFS_O_RDONLY) {
            let res = this.dirGet(file.m,
                    this.mkTag(0x7ff, 0x3ff, 0),
                    this.mkTag(LFS_TYPE_USERATTR + file.cfg.attrs[i].type,
                        file.id, file.cfg.attrs[i].size),
                        file.cfg.attrs[i].buffer);
            if (res < 0 && res != LFS_ERR_NOENT) {
                err = res;
                break main_block;
            }
        }

        // if opened for write / read-write operations
        if ((file.flags & LFS_O_WRONLY) == LFS_O_WRONLY) {
            if (file.cfg.attrs[i].size > this.attrMax) {
                err = LFS_ERR_NOSPC;
                break main_block;
            }

            file.flags |= LFS_F_DIRTY;
        }
    }

    // allocate buffer if needed
    if (file.cfg.buffer) {
        file.cache.buffer = file.cfg.buffer;
    } else {
        file.cache.buffer = new Uint8Array(this.cfg.cacheSize);
        if (!file.cache.buffer) {
            err = LFS_ERR_NOMEM;
            break main_block;
        }
    }

    // zero to avoid information leak
    this.cacheZero(file.cache);

    if (this.tagType3(tag) == LFS_TYPE_INLINESTRUCT) {
        // load inline files
        file.ctz.head = LFS_BLOCK_INLINE;
        file.ctz.size = this.tagSize(tag);
        file.flags |= LFS_F_INLINE;
        file.cache.block = file.ctz.head;
        file.cache.off = 0;
        file.cache.size = this.cfg.cacheSize;

        // don't always read (may be new/trunc file)
        if (file.ctz.size > 0) {
            let res = this.dirGet(file.m,
                        this.mkTag(0x700, 0x3ff, 0),
                        this.mkTag(LFS_TYPE_STRUCT, file.id,
                        Math.min(file.cache.size, 0x3fe)),
                        file.cache.buffer);
            if (res < 0) {
                err = res;
                break main_block;
            }
        }
    }

    return 0;
  }
//cleanup:
    // clean up lingering resources
    file.flags |= LFS_F_ERRED;
    this.fileClose(file);
    return err;
  }

  fileWrite(file, buffer, size) {
      console.assert((file.flags & LFS_O_WRONLY) == LFS_O_WRONLY);

      let data = 0;
      let nsize = size;

      if (file.flags & LFS_F_READING) {
          // drop any reads
          let err = this.fileFlush(file);
          if (err) {
              return err;
          }
      }

      if ((file.flags & LFS_O_APPEND) && file.pos < file.ctz.size) {
          file.pos = file.ctz.size;
      }

      if (file.pos + size > this.fileMax) {
          // Larger than file limit?
          return LFS_ERR_FBIG;
      }

      if (!(file.flags & LFS_F_WRITING) && file.pos > file.ctz.size) {
          // fill with zeros
          let pos = file.pos;
          file.pos = file.ctz.size;

          while (file.pos < pos) {
              let res = this.fileWrite(file, 0, 1);
              if (res < 0) {
                  return res;
              }
          }
      }

      if ((file.flags & LFS_F_INLINE) &&
              Math.max(file.pos+nsize, file.ctz.size) >
              Math.min(0x3fe, Math.min(
                  this.cfg.cacheSize,
                  (this.cfg.metadataMax ?
                      this.cfg.metadataMax : this.cfg.blockSize) / 8))) {
          // inline file doesn't fit anymore
          let err = this.fileOutline(file);
          if (err) {
              file.flags |= LFS_F_ERRED;
              return err;
          }
      }

      while (nsize > 0) {
          // check if we need a new block
          if (!(file.flags & LFS_F_WRITING) ||
                  file.off == this.cfg.blockSize) {
              if (!(file.flags & LFS_F_INLINE)) {
                  if (!(file.flags & LFS_F_WRITING) && file.pos > 0) {
                      // find out which block we're extending from
                      let err = this.ctzFind(null, file.cache,
                              file.ctz.head, file.ctz.size,
                              file.pos-1, file.block, file.off);
                      if (err) {
                          file.flags |= LFS_F_ERRED;
                          return err;
                      }

                      // mark cache as dirty since we may have read data into it
                      this.cacheZero(file.cache);
                  }

                  // extend file with new blocks
                  this.allocAck();
                  let err = this.ctzExtend(file.cache, this.rcache,
                          file.block, file.pos,
                          file.block, file.off);
                  if (err) {
                      file.flags |= LFS_F_ERRED;
                      return err;
                  }
              } else {
                  file.block = LFS_BLOCK_INLINE;
                  file.off = file.pos;
              }

              file.flags |= LFS_F_WRITING;
          }

          // program as much as we can in current block
          let diff = Math.min(nsize, this.cfg.blockSize - file.off);
 program_loop: while (true) {
            program_block: if (true) {
              let err = this.bdProg(file.cache, this.rcache, true,
                      file.block, file.off, buffer.slice(data), diff);
              if (err) {
                  if (err == LFS_ERR_CORRUPT) {
                      break program_block;
                  }
                  file.flags |= LFS_F_ERRED;
                  return err;
              }

              break program_loop;
            }
//relocate:
            let err = this.fileRelocate(file);
            if (err) {
                file.flags |= LFS_F_ERRED;
                return err;
            }
        }

        file.pos += diff;
        file.off += diff;
        data += diff;
        nsize -= diff;

        this.allocAck();
    }

    file.flags &= ~LFS_F_ERRED;
    return size;
  }

  fileClose(file) {
    let err = this.fileSync(file);

    // remove from list of mdirs
    this.mlistRemove(file);

    // clean up memory
    if (!file.cfg.buffer) {
        file.cache.buffer = null;
    }

    return err;
  }

  fileSync(file) {
    if (file.flags & LFS_F_ERRED) {
        // it's not safe to do anything if our file errored
        return 0;
    }

    let err = this.fileFlush(file);
    if (err) {
        file.flags |= LFS_F_ERRED;
        return err;
    }
    if ((file.flags & LFS_F_DIRTY) && !this.pairIsnull(file.m.pair)) {
        // update dir entry
        let type;
        let buffer;
        let size;
        let ctz = new Ctz();
        if (file.flags & LFS_F_INLINE) {
            // inline the whole file
            type = LFS_TYPE_INLINESTRUCT;
            buffer = file.cache.buffer;
            size = file.ctz.size;
        } else {
            // update the ctz reference
            type = LFS_TYPE_CTZSTRUCT;
            // copy ctz so alloc will work during a relocate
            ctz = file.ctz;
            this.ctzTole32(ctz);
            buffer = ctz;
            size = struct.calcsize("II");
        }

        // commit file data and attributes
        err = this.dirCommit(file.m, this.mkAttrs(
                [this.mkTag(type, file.id, size), buffer],
                [this.mkTag(LFS_FROM_USERATTRS, file.id, file.cfg.attrCount), file.cfg.attrs]));
        if (err) {
            file.flags |= LFS_F_ERRED;
            return err;
        }

        file.flags &= ~LFS_F_DIRTY;
    }

    return 0;

  }

  setattr(path, type, buffer, size) {
    if (size > this.attrMax) {
        return LFS_ERR_NOSPC;
    }

    return this.commitattr(path, type, buffer, size);
  }

  fileRelocate(file) {
    while (true) {
      main_block: if (true) {
        // just relocate what exists into new block
        let blockObj = new ByRef();
        let err = this.alloc(blockObj);
        let nblock = blockObj.get();
        if (err) {
            return err;
        }

        err = this.bdErase(nblock);
        if (err) {
            if (err == LFS_ERR_CORRUPT) {
                break main_block;
            }
            return err;
        }

        // either read from dirty cache or disk
        for (let i = 0; i < file.off; i++) {
            let data;
            if (file.flags & LFS_F_INLINE) {
                err = this.dirGetread(file.m,
                        // note we evict inline files before they can be dirty
                        null, file.cache, file.off-i,
                        this.mkTag(0xfff, 0x1ff, 0),
                        this.mkTag(LFS_TYPE_INLINESTRUCT, file.id, 0),
                        i, data, 1);
                if (err) {
                    return err;
                }
            } else {
                var bufferByRef = new ByRef();
                err = this.bdRead(file.cache, this.rcache, file.off-i,
                        file.block, i, bufferByRef, 1);
                data = bufferByRef.get();
                if (err) {
                    return err;
                }
            }

            err = this.bdProg(this.pcache, this.rcache, true,
                    nblock, i, data, 1);
            if (err) {
                if (err == LFS_ERR_CORRUPT) {
                    break main_block;
                }
                return err;
            }
        }

        // copy over new state of file
        //memcpy(file.cache.buffer, this.pcache.buffer, this.cfg.cacheSize);
        file.cache.buffer.set(this.pcache.buffer.slice(0, this.cfg.cacheSize));

        file.cache.block = this.pcache.block;
        file.cache.off = this.pcache.off;
        file.cache.size = this.pcache.size;
        this.cacheZero(this.pcache);

        file.block = nblock;
        file.flags |= LFS_F_WRITING;
        return 0;
      }
//relocate:
        console.warn("Bad block at " + toHex(nblock, 8));

        // just clear cache and try a new block
        this.cacheDrop(this.pcache);
    }
  }

  fileOutline(file) {
    file.off = file.pos;
    this.allocAck();
    let err = this.fileRelocate(file);
    if (err) {
        return err;
    }

    file.flags &= ~LFS_F_INLINE;
    return 0;
  }

  fileFlush(file) {
    if (file.flags & LFS_F_READING) {
        if (!(file.flags & LFS_F_INLINE)) {
            this.cacheDrop(file.cache);
        }
        file.flags &= ~LFS_F_READING;
    }

    if (file.flags & LFS_F_WRITING) {
        let pos = file.pos;

        if (!(file.flags & LFS_F_INLINE)) {
            // copy over anything after current branch
            let orig = new LfsFile({
                ctz: file.ctz,
                flags: LFS_O_RDONLY,
                pos: file.pos,
                cache: this.rcache,
            });
            this.cacheDrop(this.rcache);

            while (file.pos < file.ctz.size) {
                // copy over a byte at a time, leave it up to caching
                // to make this efficient
                let data;
                let res = this.fileRead(orig, data, 1);
                if (res < 0) {
                    return res;
                }

                res = this.fileWrite(file, data, 1);
                if (res < 0) {
                    return res;
                }

                // keep our reference to the rcache in sync
                if (this.rcache.block != LFS_BLOCK_NULL) {
                    this.cacheDrop(orig.cache);
                    this.cacheDrop(this.rcache);
                }
            }

            // write out what we have
            while (true) {
                let err = this.bdFlush(file.cache, this.rcache, true);
                if (!err) {
                  break;
                }
                if (err != LFS_ERR_CORRUPT) {
                    return err;
                }

                console.warn("Bad block at " + toHex(file.block, 8));
                err = this.fileRelocate(file);
                if (err) {
                    return err;
                }
            }
        } else {
            file.pos = Math.max(file.pos, file.ctz.size);
        }

        // actual file updates
        file.ctz.head = file.block;
        file.ctz.size = file.pos;
        file.flags &= ~LFS_F_WRITING;
        file.flags |= LFS_F_DIRTY;

        file.pos = pos;
    }

    return 0;
  }

  mlistRemove(mlist) {
    for (let p = this.mlist; p; p = p.next) {
      if (p == mlist) {
          p = p.next;
          break;
      }
    }
  }

  mlistAppend(mList) {
    mList.next = this.mList;
    this.mList = mList;
  }

  commitattr(path, type, buffer, size) {
    let cwd = new MDir();
    let pathByRef = new ByRef(path);
    let tag = this.dirFind(cwd, pathByRef, new ByRef(null));
    path = pathByRef.get();
    if (tag < 0) {
        return tag;
    }

    let id = this.tagId(tag);
    if (id == 0x3ff) {
        // special case for root
        id = 0;
        let err = this.dirFetch(cwd, this.root);
        if (err) {
            return err;
        }
    }
    return this.dirCommit(cwd, this.mkAttrs([this.mkTag(LFS_TYPE_USERATTR + type.charCodeAt(0), id, size), buffer]));
  }

  dirCommitprog(commit, buffer, size) {
    let err = this.bdProg(this.pcache, this.rcache, false,
            commit.block, commit.off, buffer, size);
    if (err) {
        return err;
    }

    commit.crc = this.crc(commit.crc, buffer, size);
    commit.off += size;
    return 0;
  }

  fsForceconsistency() {
    let err = this.fsDemove();
    if (err) {
        return err;
    }

    err = this.fsDeorphan();
    if (err) {
        return err;
    }

    return 0;
  }

  fsDemove() {
    if (!this.gstateHasmove(this.gdisk)) {
        return 0;
    }

    // Fix bad moves
    console.warn("Fixing move {" +
                toHex(this.gdisk.pair[0], 8) + ", " +
                toHex(this.gdisk.pair[1], 8) + "} " +
                toHex(this.tagId(this.gdisk.tag), 4));

    // fetch and delete the moved entry
    let movedir = new MDir();
    let err = this.dirFetch(movedir, this.gdisk.pair);
    if (err) {
        return err;
    }

    // prep gstate and delete move id
    let moveid = this.tagId(this.gdisk.tag);
    this.fsPrepmove(0x3ff, null);
    err = this.dirCommit(movedir, this.mkAttrs(
            [this.mkTag(LFS_TYPE_DELETE, moveid, 0), null]));
    if (err) {
        return err;
    }

    return 0;
  }

  fsDeorphan() {
    if (!this.gstateHasorphans(this.gstate)) {
        return 0;
    }

    // Fix any orphans
    let pdir = new MDir({split: true, tail: [0, 1]});
    let dir = new MDir();

    // iterate over all directory directory entries
    while (!this.pairIsnull(pdir.tail)) {
        let err = this.dirFetch(dir, pdir.tail);
        if (err) {
            return err;
        }

        // check head blocks for orphans
        if (!pdir.split) {
            // check if we have a parent
            let parent = new MDir();
            let tag = this.fsParent(pdir.tail, parent);
            if (tag < 0 && tag != LFS_ERR_NOENT) {
                return tag;
            }

            if (tag == LFS_ERR_NOENT) {
                // we are an orphan
                console.warn("Fixing orphan {" +
                            toHex(pdir.tail[0], 8) + ", " +
                            toHex(pdir.tail[1], 8) + "}");
                err = this.dirDrop(pdir, dir);
                if (err) {
                    return err;
                }

                // refetch tail
                continue;
            }

            let pair = new Array(2);
            let res = this.dirGet(parent,
                    this.mkTag(0x7ff, 0x3ff, 0), tag, pair);
            if (res < 0) {
                return res;
            }
            this.pairFromle32(pair);

            if (!this.pairSync(pair, pdir.tail)) {
                // we have desynced
                console.warn("Fixing half-orphan {" +
                            toHex(pdir.tail[0], 8) + ", " +
                            toHex(pdir.tail[1], 8) + "} -> {" +
                            toHex(pair[0], 8) + ", " +
                            toHex(pair[1], 8) + "}");

                this.pairTole32(pair);
                err = this.dirCommit(pdir, this.mkAttrs(
                        [this.mkTag(LFS_TYPE_SOFTTAIL, 0x3ff, 8), pair]));
                this.pairFromle32(pair);
                if (err) {
                    return err;
                }

                // refetch tail
                continue;
            }
        }

        pdir = dir;
    }

    // mark orphans as fixed
    return this.fsPreporphans(-this.gstateGetorphans(this.gstate));

  }

  ctzFind() {
    console.warn("ctzFind not implemented");
  }

  ctzExtend() {
    console.warn("ctzExtend not implemented");
  }

  ctzTraverse() {
    console.warn("ctzTraverse not implemented");
  }

  fsPreporphans() {
    console.warn("fsPreporphans not implemented");
  }

  fsPrepmove() {
    console.warn("fsPrepmove not implemented");
  }

  fsParent() {
    console.warn("fsParent not implemented");
  }

  pairSync() {
    console.warn("pairSync not implemented");
  }

  mkdir(path) {
    // deorphan if we haven't yet, needed at most once after poweron
    let err = this.fsForceconsistency();
    if (err) {
        return err;
    }

    let cwd = new MList();
    cwd.next = this.mlist;
    let idByRef = new ByRef();
    let pathByRef = new ByRef(path);
    err = this.dirFind(cwd.m, pathByRef, idByRef);
    path = pathByRef.get();
    let id = idByRef.get();

    if (!(err == LFS_ERR_NOENT && id != 0x3ff)) {
        return (err < 0) ? err : LFS_ERR_EXIST;
    }

    // check that name fits
    let nlen = path.length;
    if (nlen > this.nameMax) {
        return LFS_ERR_NAMETOOLONG;
    }

    // build up new directory
    this.allocAck();
    dir = new MDir();
    err = this.dirAlloc(dir);
    if (err) {
        return err;
    }

    // find end of list
    let pred = cwd.m;
    while (pred.split) {
        err = lfs_dir_fetch(pred, pred.tail);
        if (err) {
            return err;
        }
    }

    // setup dir
    this.pairTole32(pred.tail);
    err = this.dirCommit(dir, this.mkAttrs(
            [this.mkTag(LFS_TYPE_SOFTTAIL, 0x3ff, 8), pred.tail]));
    this.pairFromle32(pred.tail);
    if (err) {
        return err;
    }

    // current block end of list?
    if (cwd.m.split) {
        // update tails, this creates a desync
        err = this.fsPreporphans(+1);
        if (err) {
            return err;
        }

        // it's possible our predecessor has to be relocated, and if
        // our parent is our predecessor's predecessor, this could have
        // caused our parent to go out of date, fortunately we can hook
        // ourselves into littlefs to catch this
        cwd.type = 0;
        cwd.id = 0;
        this.mlist = cwd;

        this.pairTole32(dir.pair);
        err = this.dirCommit(pred, this.mkAttrs(
                [this.mkTag(LFS_TYPE_SOFTTAIL, 0x3ff, 8), dir.pair]));
        this.pairFromle32(dir.pair);
        if (err) {
            this.mlist = cwd.next;
            return err;
        }

        this.mlist = cwd.next;
        err = this.fsPreporphans(-1);
        if (err) {
            return err;
        }
    }

    // now insert into our parent block
    this.pairTole32(dir.pair);
    err = this.dirCommit(cwd.m, this.mkAttrs(
            [this.mkTag(LFS_TYPE_CREATE, id, 0), null],
            [this.mkTag(LFS_TYPE_DIR, id, nlen), path],
            [this.mkTag(LFS_TYPE_DIRSTRUCT, id, 8), dir.pair],
            [this.mkTagIf(!cwd.m.split, LFS_TYPE_SOFTTAIL, 0x3ff, 8), dir.pair]
          ));
    this.pairFromle32(dir.pair);
    if (err) {
        return err;
    }

    return 0;
  }

  mkTag(type, id, size) {
    return ((type << 20) | (id << 10) | size) >>> 0;
  }

  mkTagIf(cond, type, id, size) {
    return cond ? this.mkTag(type, id, size) : this.mkTag(LFS_FROM_NOOP, 0, 0);
  }

  mkTagIfElse(cond, type1, id1, size1, type2, id2, size2) {
    return cond ? this.mkTag(type1, id1, size1) : this.mkTag(type2, id2, size2);
  }

  mkAttrs(...args) {
    let attrs = [];
    for (let [tag, buffer] of args) {
      attrs.push(new MAttr({tag: tag, buffer: buffer}));
    }
    return attrs;
  }

  copyObjProps(toObject, fromObject) {
    for (var key in fromObject) {
      if (fromObject.hasOwnProperty(key)) {
         toObject[key] = fromObject[key];
      }
    }
  }
}

class LfsConfig {
  constructor({
    context = null,
    readSize = 64,
    progSize = 64,
    blockSize = 0,
    blockCount = 0,
    blockCycles = 16,
    cacheSize = 64,
    lookaheadSize = 64,
    nameMax = LFS_NAME_MAX,
    fileMax = LFS_FILE_MAX,
    attrMax = LFS_ATTR_MAX,
    flash = flash
  }={}) {
    this.context = context;
    this.readSize = readSize;
    this.progSize = progSize;
    this.blockSize = blockSize;
    this.blockCount = blockCount;
    this.blockCycles = blockCycles;
    this.cacheSize = cacheSize;
    this.lookaheadSize = lookaheadSize;
    this.nameMax = nameMax;
    this.fileMax = fileMax;
    this.attrMax = attrMax;
    this.metadataMax = this.blockSize;
    this.flash = flash
  }

  // Read a region in a block. Negative error codes are propagated
  // to the user.
  read(block, off, buffer, size) {
    //memcpy(buffer, this.flash[0] + this.blockSize * block + off, size);
    buffer.set(this.flash.data.slice(this.blockSize * block + off, this.blockSize * block + off + size));
    return 0;
  }

  // Program a region in a block. The block must have previously
  // been erased. Negative error codes are propagated to the user.
  // May return LFS_ERR_CORRUPT if the block should be considered bad.
  prog(block, off, buffer, size) {
    //memcpy(&s_flashmem[0] + block * this.blockSize + off, buffer, size);
    this.flash.data.set(buffer.slice(0, size), this.blockSize * block + off);
    return 0;
  }

  // Erase a block. A block must be erased before being programmed.
  // The state of an erased block is undefined. Negative error codes
  // are propagated to the user.
  // May return LFS_ERR_CORRUPT if the block should be considered bad.
  erase(block) {
    //memset(&s_flashmem[0] + block * this.blockSize, 0, this.blockSize);
    this.flash.data.set(new Uint8Array(this.blockSize).fill(0), this.blockSize * block);
    return 0;
  }

  // Sync the state of the underlying block device. Negative error codes
  // are propagated to the user.
  sync() {
    return 0;
  }

  // Optional statically allocated read buffer. Must be cache_size.
  // By default lfs_malloc is used to allocate this buffer.
  readBuffer = null;

  // Optional statically allocated program buffer. Must be cache_size.
  // By default lfs_malloc is used to allocate this buffer.
  progBuffer = null;

  // Optional statically allocated lookahead buffer. Must be lookahead_size
  // and aligned to a 32-bit boundary. By default lfs_malloc is used to
  // allocate this buffer.
  lookaheadBuffer = null;
}

class SuperBlock {
  constructor({
    version = 0,
    blockSize = 0,
    blockCount = 0,
    nameMax = 0,
    fileMax = 0,
    attrMax = 0
  } = {}) {
    this.version = version;
    this.blockSize = blockSize;
    this.blockCount = blockCount;
    this.nameMax = nameMax;
    this.fileMax = fileMax;
    this.attrMax = attrMax;
  }

  setFromBuffer(buffer) {
    let items = LittleFS.bufferToUint(buffer, struct.calcsize("IIIIII"));
    Object.keys(this).forEach((key, index) => {
      this[key] = items[index];
    });
  }
}

class ByRef {
  constructor(data = undefined) {
    this.data = data;
  }

  set(value) {
    this.data = value;
  }

  get() {
    return this.data;
  }
}

class GState {
  constructor({
    tag = 0,
    pair = [0, 0]
  } = {}) {
    this.tag = tag;
    this.pair = pair;
  }
}

class MList {
  constructor({
    id = 0,
    type = 0,
    m = new MDir()
  } = {}) {
    this.id = id;
    this.type = type;
    this.m = m;
    this.next = null;
  }
}

class MDir {
  constructor({
    pair = [0, 0],
    rev = 0,
    off = 0,
    etag = 0,
    count = 0,
    erased = false,
    split = false,
    tail = [0, 0]
  } = {}) {
    this.pair = pair;
    this.rev = rev;
    this.off = off;
    this.etag = etag;
    this.count = count;
    this.erased = erased;
    this.split = split;
    this.tail = tail;
  }
}

class MAttr {
  constructor({
    tag = null,
    buffer = null
  } = {}) {
    this.tag = tag;
    this.buffer = buffer;
  }
}

class Attr {
  constructor({
    type = 0,
    buffer = null,
    size = 0
  } = {}) {
    this.type = type;
    this.buffer = buffer;
    this.size = size;
  }
}

class Diskoff {
  constructor({
    block,
    off
  } = {}) {
    this.block = block;
    this.off = off;
  }
};

class Ctz {
  constructor({head = null, size = 0} = {}) {
    this.head = head;
    this.size = size;
  }
  setFromBuffer(buffer) {
    let items = LittleFS.bufferToUint(buffer, struct.calcsize("II"));
    Object.keys(this).forEach((key, index) => {
      this[key] = items[index];
    });
  }
}

class DirFindMatch {
  constructor({name = null, size = 0} = {}) {
    this.name = name;
    this.size = size;
  }
};

class Commit {
  constructor({
    block = 0,
    off = 0,
    ptag = 0,
    crc = 0,
    begin = 0,
    end = 0
  } = {}) {
    this.block = block;
    this.off = off;
    this.ptag = ptag;
    this.crc = crc;
    this.begin = begin;
    this.end = end;
  }
};

class Cache {
  constructor({
    block = LFS_BLOCK_NULL,
    off = 0,
    size = 0,
    buffer = null,
  } = {}) {
    this.block = block;
    this.off = off;
    this.size = size;
    this.buffer = buffer;
  }
};

class FileConfig {
  constructor({
    buffer = null,
    attrs = [],
    attrCount = 0
  } = {}) {
    this.buffer = buffer;
    this.attrs = attrs;
    this.attrCount = attrCount;
  }
}

class LfsFile {
  constructor({
    id = 1,
    type = 0,
    m = new MDir(),
    ctz = new Ctz(),
    flags = 0,
    pos = 0,
    block = 0,
    off = 0,
    cache = new Cache(),
    cfg = new FileConfig()
  } = {}) {
    this.id = id;
    this.type = type;
    this.m = m;
    this.ctz = ctz;
    this.flags = flags;
    this.pos = pos;
    this.block = block;
    this.off = off;
    this.cache = cache;
    this.cfg = cfg;
    this.next = null;
  }
};

class struct {
    static lut = {
      "b": {u: DataView.prototype.getInt8, p: DataView.prototype.setInt8, bytes: 1},
      "B": {u: DataView.prototype.getUint8, p: DataView.prototype.setUint8, bytes: 1},
      "h": {u: DataView.prototype.getInt16, p: DataView.prototype.setInt16, bytes: 2},
      "H": {u: DataView.prototype.getUint16, p: DataView.prototype.setUint16, bytes: 2},
      "i": {u: DataView.prototype.getInt32, p: DataView.prototype.setInt32, bytes: 4},
      "I": {u: DataView.prototype.getUint32, p: DataView.prototype.setUint32, bytes: 4},
      "q": {u: DataView.prototype.getInt64, p: DataView.prototype.setInt64, bytes: 8},
      "Q": {u: DataView.prototype.getUint64, p: DataView.prototype.setUint64, bytes: 8},
    }

    static pack(...args) {
        let format = args[0];
        let pointer = 0;
        let data = args.slice(1);
        if (format.replace(/[<>]/, '').length != data.length) {
            throw("Pack format to Argument count mismatch");
            return;
        }
        let bytes = [];
        let littleEndian = true;
        for (let i = 0; i < format.length; i++) {
            if (format[i] == "<") {
                littleEndian = true;
            } else if (format[i] == ">") {
                littleEndian = false;
            } else {
                pushBytes(format[i], data[pointer]);
                pointer++;
            }
        }

        function pushBytes(formatChar, value) {
            if (!(formatChar in struct.lut)) {
                throw("Unhandled character '" + formatChar + "' in pack format");
            }
            let dataSize = struct.lut[formatChar].bytes;
            let view = new DataView(new ArrayBuffer(dataSize));
            let dataViewFn = struct.lut[formatChar].p.bind(view);
            dataViewFn(0, value, littleEndian);
            for (let i = 0; i < dataSize; i++) {
                bytes.push(view.getUint8(i));
            }
        }

        return bytes;
    };

    static unpack(format, bytes) {
        let pointer = 0;
        let data = [];
        let littleEndian = true;

        for (let c of format) {
            if (c == "<") {
                littleEndian = true;
            } else if (c == ">") {
                littleEndian = false;
            } else {
                pushData(c);
            }
        }

        function pushData(formatChar) {
            if (!(formatChar in struct.lut)) {
                throw("Unhandled character '" + formatChar + "' in unpack format");
            }
            let dataSize = struct.lut[formatChar].bytes;
            let view = new DataView(new ArrayBuffer(dataSize));
            for (let i = 0; i < dataSize; i++) {
              view.setUint8(i, bytes[pointer + i] & 0xFF);
            }
            let dataViewFn = struct.lut[formatChar].u.bind(view);
            data.push(dataViewFn(0, littleEndian));
            pointer += dataSize;
        }

        return data;
    };

    static calcsize(format) {
        let size = 0;
        for (let i = 0; i < format.length; i++) {
            if (format[i] != "<" && format[i] != ">") {
                size += struct.lut[format[i]].bytes;
            }
        }

        return size;
    }
}

export { LittleFS, LfsConfig, LfsFile, LFS_O_RDONLY, LFS_O_WRONLY, LFS_O_RDWR, LFS_O_CREAT, LFS_O_EXCL, LFS_O_TRUNC, LFS_O_APPEND };
