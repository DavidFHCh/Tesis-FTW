Makefile para un proyecto en Coq:
1- crear un archivo titulado "\_CoqProject" con la siguiente linea y los archivos con su extension .v
   -R . MiProyecto
   el proyecto tendra por titulo MiProyecto
2- para crear el makefile, desde una terminal ingresar la siguiente linea
   coq_makefile -f \_CoqProyect -o Makefile
3- el archivo se creara con el nombre Makefile y
   para iniciar coqide con las rutas correctas para las dependencias 
   se debe ejecutar mediante: 
   coqide -R . MiProyecto miarchivo.v 
   
-----------------------------------
De los archivos de Graciela Lopez Campos 

Los preliminares son: 
AB.hs --> Sec 1.3   y   
ABB.has --> Sec 1.4

Los archivos a traducir a Coq son:
+ ARNo.hs --> Sec 2.1
+ ARNci1.hs --> Sec 3.1
+ ARNci2.hs --> Sec 3.2
+ ARNac.hs --> Sec 3.3
+ ARTa_V2_set.hs --> Sec 3.4
+ ARTa.hs --> Sec 3.4
