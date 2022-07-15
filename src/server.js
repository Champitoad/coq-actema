const net = require('net');
const fs = require('fs');

const server = net.createServer((c) => {
  // 'connection' listener.
  console.log('client connected');
  c.on('end', () => {
    console.log('client disconnected');
  });
  c.write('hello\r\n');
  c.pipe(fs.createWriteStream('client.log'));
});
server.on('error', (err) => {
  throw err;
});

export default {
  launch: function () {
    server.listen(8124, () => {
      console.log('server bound');
    });
  }
}
