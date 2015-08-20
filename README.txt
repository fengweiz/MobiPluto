This is the source code of MobiPluto.
Before using this code, you should read the ACSAC paper: MobiPluto: File System Friendly Deniable Storage for Mobile Devices.

You can get the whole AOSP code from http://source.android.com/source/downloading.html.
Note that we use Android 4.2.2 and LG Nexus 4 to implement our prototype.

You should put CommandListener.cpp, cryptfs.c and cryptfs.h in [ANDROID-SRC]/system/vold/ and replace the original files.

Before you compile the code, you should get a modified Linux kernel. You can get the source code here http://source.android.com/source/building-kernels.html. You should enable XTS, gf128mul and Thin Provisioning when configuring the kernel. Place the kernel image in the [ANDROID-SRC]/device/[VENDOR]/[PRODUCT]/ directory. The file must be named "kernel". For example, the Nexus 4 kernel binary should be placed at [ANDROID-SRC]/device/lge/mako/kernel.

Then you can compile the Android code.

After you compile the code, you should use Android Image Kitchen(http://forum.xda-developers.com/showthread.php?t=2073775) to modify boot.img.

You should put init.mako.rc to [BOOT]/ramdisk/ and replace the old one. What's more, you should compile LVM and thin provisioning tools for Android and put them in boot.img. You can get the source code from https://github.com/steven676/android-lvm-mod and https://github.com/jthornber/thin-provisioning-tools. You may get some help from https://raw.githubusercontent.com/steven676/android-lvm-mod/master/HOWTO-BUILD.

After you compile LVM and thin provisioning tools, you should put lvm in [BOOT]/ramdisk/lvm/sbin/, lvm.conf in [BOOT]/ramdisk/lvm/etc, thin_check, thin_metadata_size and thin_rmap in [BOOT]/ramdisk/usr/sbin. Create the directory that you need. Then you can get the modified boot.img.

Flash your phone with the new images and enjoy MobiPluto!

I will work on improving the code.

I want to thank the outstanding work Mobiflage which is a open-source project proposed by Adam Skillen.
Mobiflage is available at https://www.ccsl.carleton.ca/~askillen/mobiflage/
Additionally, I want to thank the authors of the works mentioned above.

Bing Chang
Institute of Information Engineering, Chinese Academy of Sciences, China
changbing@iie.ac.cn