# `annotated-upstream/` is the SHA-3 crate of upstream libcrux-iot at the
# commit below, with the patches in `annotation-patches/` applied: the ones hax
# needs to extract it to Lean, and the contracts that name the specification.
#
#   make          fetch the crate and apply the patches (the same as
#                 `make annotated-upstream`)
#   make fetch    replace `annotated-upstream/` with the pristine upstream crate
#                 and upstream's `LICENSE`
#   make patch    apply `annotation-patches/*.patch`, in order, to
#                 `annotated-upstream/`
#   make check    regenerate `annotated-upstream/` and fail if it differs from
#                 what is in git

REPO    := celabshq/libcrux-iot
COMMIT  := 5df472a16187bdf12675191c0eca21e801365c25
URL     := https://codeload.github.com/$(REPO)/tar.gz/$(COMMIT)
TOP     := libcrux-iot-$(COMMIT)
CRATE   := $(TOP)/libcrux-iot/sha3
SOURCE  := annotated-upstream
PATCHES := $(sort $(wildcard annotation-patches/*.patch))

.PHONY: $(SOURCE) fetch patch check

# `patch` runs only after `fetch` has finished, also under `make -j`.
$(SOURCE): fetch
	$(MAKE) patch

# Upstream's `proofs/` holds its own F* development, which is not used here.
# The crate is AGPL-3.0-only, but the license text sits at the root of
# upstream's repository rather than in the crate, so it is extracted next to
# the crate separately.
fetch:
	rm -rf $(SOURCE)
	mkdir -p $(SOURCE)
	tmp=$$(mktemp) && trap 'rm -f "$$tmp"' EXIT \
		&& curl -fsSL -o "$$tmp" $(URL) \
		&& tar -xzf "$$tmp" -C $(SOURCE) --strip-components=3 \
			--exclude='$(CRATE)/proofs' '$(CRATE)' \
		&& tar -xzOf "$$tmp" '$(TOP)/LICENSE' > $(SOURCE)/LICENSE

# Each patch is checked with a dry run first, so that one that does not apply
# leaves `annotated-upstream/` untouched instead of half-patched.
patch:
	@for p in $(PATCHES); do \
		echo "applying $$p"; \
		patch -d $(SOURCE) -p1 --forward --silent --dry-run < $$p \
			&& patch -d $(SOURCE) -p1 --forward --silent < $$p \
			|| exit 1; \
	done

# Compares with the index, which is what is committed once `annotated-upstream/` is.
check: $(SOURCE)
	@git diff --exit-code -- $(SOURCE)
	@test -z "$$(git ls-files --others --exclude-standard -- $(SOURCE))" \
		|| { git ls-files --others --exclude-standard -- $(SOURCE); exit 1; }
