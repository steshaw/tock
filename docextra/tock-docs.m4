m4_dnl  Macros to make Tock's HTML documentation a bit nicer.

m4_define(`_tock_svg',`<object data="$1.svg" width="$2" height="$3">
<em>
In order to view this image you need an SVG viewer.  The most recent
versions of Firefox and Opera both have in-built SVG viewers.  For Internet
Explorer, you will need to install the <a
href="http://www.adobe.com/svg/viewer/install/">Adobe SVG Viewer</a>.
</em>
</object>')
