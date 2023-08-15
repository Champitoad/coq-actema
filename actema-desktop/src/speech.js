import { ipcMain } from 'electron';
import { connect } from 'http2';

// "ipc" in "ipcMain" stands for "Inter-Process Communication": this is the
// object that enables communication between the Renderer process (the browser
// window) and the Main process, which is allowed to perform system calls.

// Here we use ipcMain to bind event listeners to the Main process: they will be
// triggered from the Renderer process (e.g. in index.vue) so that we can send
// TCP requests to the Python speech daemon when entering speech recognition
// mode in the interface.

const net = require('net');
const Port = 42000;
var client;
var State = 0;


export default {
    startDaemon: function (win) {
      // TODO
    },
    bindEvents: function (win) {
        // Bind a listener to a new event named "vocalCommand", which just sends
        // back the sentence spoken by the user to the Renderer. The logic of
        // listening in a loop until a valid command is uttered is implemented
        // in the Renderer, so that we can request the list of available actions
        // from Actema's proof engine.
        ipcMain.on('vocalCommand', _ => {
            // TODO: code qui envoie la requête de commande vocale au script
            // Python, récupère la réponse sous forme de string, et l'envoie au
            // Renderer process.

            // Pour communiquer avec le Renderer, il faudra utiliser la fonction
            // win.webContents.send('vocalCommand', <command>), où <command> est
            // la string en question.

            /*
            client = new net.Socket();
            client.connect({ port: Port, host: "localhost" });
            client.on("data", (data) => {
                var s = data.toString("utf-8");
                console.log(s, levenshteinDistance(s, "induction"));
              })
            client.write('test!');
            */



            console.log("selected smth");
        });

        // Bind a listener to a new event named "stopListening", which instructs
        // the speech daemon to stop trying to recognize sentences.
        ipcMain.on('stopSpeechRecognition', _ => {
            // TODO

            /*
            client = new net.Socket();
            client.connect({ port: Port, host: "localhost" });
            client.on("data", (data) => {
                console.log(data.toString("utf-8"))
              })
            client.write('stop!');
            */
           State = 0;

            
            console.log("Stopping speech recognition");
        });

        ipcMain.on('startSpeechRecognition', _ => {
          /*
            // TODO
            client = new net.Socket();
            client.connect({ port: Port, host: "localhost" });
            client.on("data", (data) => {
                console.log(data.toString("utf-8"))
              })
            client.write('start!');
          */

            State = 1;
            client = new net.Socket();
            client.connect({ port: Port, host: "localhost" });
            client.on("data", (data) => {
              if (State){
                var s = data.toString("utf-8");
                console.log(s);
                win.webContents.send('TEST', s);
                /*
                const arr = [];
                var n = search_box.length;
                for (let i = 0; i < n; i++) {
                  arr[i] = levenshteinDistance(s, search_box[i]);
                }
                console.log(arr);*/
              }
              })
            client.write('start and listen!');

            
            console.log("Starting speech recognition");
        });
    }
}

