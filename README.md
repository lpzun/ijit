## Introduction
IJIT (**I**nterface for **J**ust-**I**n-**T**ime translation) is an API 
which helps users to transform their [transition-system] based algorithms 
to a version that can operate directly on [Boolean Programs]. Said an API 
avoids converting a Boolean program to a transition system up front, as 
up-front conversion usually incurs state space blowup.

## Get Started

### Source Code
* Is here on [github](https://github.com/lpzun/ijit).

**REMARK**: `master` is the official branch and all new contributions 
including bugfixes are added to `master` directly. A new branch `stable` 
that contains only stable commits is coming soon.

### Install
Assuming you have downloaded [IJIT](https://github.com/lpzun/ijit), then 

>     mkdir build
>     cd build
>     cmake "Unix Makefiles" ..
>     make
>     sudo make install

By default, it will install IJIT library `DESTDIR/lib`, and include files at 
`DESTDIR/include`, where `DESTDIR` installation prefix . It is usually `/usr` 
for most Linux distros, and `/usr/local` for FreeBSD and OSX. Use the `DESTDIR=` 
command line option to change the install prefix. For example:

>     make install DESTDIR="/your/path/"

### Uninstall
Run the following command to uninstall the library:

>     sudo make uninstall

### Usage
* [API documentation](https://github.com/lpzun/ijit/wiki/Documentation)
* [Online tutorials](https://github.com/lpzun/ijit/wiki/Tutorial)


## Contribute
[Peizun Liu](https://github.com/lpzun) and [Thomas Wahl] (http://www.ccs.neu.edu/home/wahl/) are the main contributors. Peizun Liu is the main developer. 

## License
The IJIT downloads on this site are available from [github](https://github.com/lpzun/ijit) under the [MIT license](https://github.com/lpzun/ijit/blob/master/LICENSE).

## Support or Contact
Having trouble with Pages? Check out our [documentation](http://lpzun.github.io/ijit/) or [contact support](http://www.ccs.neu.edu/home/lpzun/) and we’ll help you sort it out.
