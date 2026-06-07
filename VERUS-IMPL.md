# Installing Verus

See `verus/INSTALL.md` for instructions on installing Verus.

Or use the pre-built docker image:

```
docker load -i verus-impl-docker-image.tar
```

Open a shell:

```
docker run -it verus /bin/bash
```

And run Verus from the shell, e.g.,:

```
# verus ../examples/recursion.rs 
verification results:: 11 verified, 0 errors
```
